//! The SNASM object file format.
//!
//! A SNASM object consists of a set of *blocks*, which contain a mixture of
//! data and code. Each block has a designated starting address in ROM.
//! Each block may define a number of relocations, describing to the linker
//! what information is missing to link this object into a ROM.
//!
//! Additionally, each object advertises a list of global symbols for use by the
//! linker.

use std::collections::HashMap;
use std::convert::TryInto;
use std::io;
use std::path::Path;

use serde::Deserialize;
use serde::Serialize;

use crate::int::u24;
use crate::int::Int;
use crate::isa::Instruction;
use crate::syn::fmt;
use crate::syn::operand::Symbol;

/// An assembled object file.
///
/// An `Object` is made up of a collection of `Block`s, each of which starts at
/// a different 24-bit address.
#[derive(Debug)]
pub struct Object<'asm> {
  name: &'asm Path,
  blocks: HashMap<u24, Block<'asm>>,
  globals: Vec<(Symbol<'asm>, u24)>,
}

impl<'asm> Object<'asm> {
  /// Creates a new, empty `Object`.
  pub fn new(name: &'asm (impl AsRef<Path> + ?Sized)) -> Self {
    Object {
      name: name.as_ref(),
      blocks: HashMap::new(),
      globals: Vec::new(),
    }
  }

  /// Returns the file name of this object.
  ///
  /// This is the same as the name of the file that the object was assembled
  /// from.
  pub fn file_name(&self) -> &'asm Path {
    self.name
  }

  /// Creates a new, empty block at the given starting address.
  pub fn new_block(&mut self, start: u24) -> &mut Block<'asm> {
    self.blocks.entry(start).or_insert(Block::new(start))
  }

  /// Gets a reference to the block at the given starting address, if it exists.
  pub fn get_block(&self, start: u24) -> Option<&Block<'asm>> {
    self.blocks.get(&start)
  }

  /// Gets a mutable reference to the block at the given starting address, if
  /// it exists.
  pub fn get_block_mut(&mut self, start: u24) -> Option<&mut Block<'asm>> {
    self.blocks.get_mut(&start)
  }

  /// Returns an iterator over all the blocks in this object.
  pub fn blocks(&self) -> impl Iterator<Item = (u24, &Block<'asm>)> {
    self.blocks.iter().map(|(k, v)| (*k, v))
  }

  /// Returns an iterator over all the blocks in this object.
  pub fn blocks_mut(
    &mut self,
  ) -> impl Iterator<Item = (u24, &mut Block<'asm>)> {
    self.blocks.iter_mut().map(|(k, v)| (*k, v))
  }

  /// Defines a new global symbol for this object with the given address.
  pub fn define_global(&mut self, symbol: Symbol<'asm>, addr: u24) {
    self.globals.push((symbol, addr))
  }

  /// Returns an iterator over all global symbols defined by this object.
  pub fn globals<'a>(
    &'a self,
  ) -> impl Iterator<Item = (Symbol<'asm>, u24)> + 'a {
    self.globals.iter().copied()
  }

  /// Dumps this object in the style of `objdump` to `w`.
  pub fn dump(&self, mut w: impl io::Write) -> io::Result<()> {
    for (name, addr) in &self.globals {
      writeln!(w, ".global {}, 0x{:06x}", name, addr)?;
    }
    let mut block_addrs =
      self.blocks.iter().map(|(k, _)| *k).collect::<Vec<_>>();
    block_addrs.sort();

    for addr in block_addrs {
      let block = self.get_block(addr).unwrap();
      if block.len() == 0 {
        continue;
      }
      writeln!(w, ".origin 0x{:06x}", addr)?;
      for i in 0..block.offsets.len() {
        let offset = block.offsets[i];
        let start = offset.start as usize;
        let end = block
          .offsets
          .get(i + 1)
          .map(|offset| offset.start as usize)
          .unwrap_or(block.data.len());

        match offset.ty {
          OffsetType::Code => {
            let mut addr = addr.to_u32() + start as u32;
            for instruction in Instruction::stream(&block.data[start..end]) {
              let instruction = instruction?;

              write!(w, "{:06x}:", addr)?;
              for byte in instruction.bytes() {
                write!(w, "  {:02x}", byte)?;
              }

              let expected_len = instruction.encoded_len() * 4;
              let padding = 16 - expected_len;
              for _ in 0..padding {
                write!(w, " ")?;
              }

              addr += instruction.encoded_len() as u32;
              fmt::print_instruction(
                fmt::Options::default(),
                instruction,
                &mut w,
              )?;
              writeln!(w, "")?;
            }
          }
          OffsetType::Data => {
            for (n, j) in (start..end).into_iter().enumerate() {
              if n % 8 == 0 {
                if n != 0 {
                  writeln!(w, "")?;
                }
                write!(w, "{:06x}:", addr.to_u32() + start as u32 + n as u32)?;
              }
              write!(w, "  {:02x}", block.data[j])?;
            }
            writeln!(w, "")?;
          }
        }
      }

      for relocation in &block.relocations {
        match relocation.info.ty {
          RelocationType::Absolute => writeln!(
            w,
            ".reloc.i24 0x{:04x} {}",
            relocation.info.offset, relocation.source
          )?,
          RelocationType::BankRelative(bank) => writeln!(
            w,
            ".reloc.i16 0x{:04x} {}@{:02x}",
            relocation.info.offset, relocation.source, bank
          )?,
          RelocationType::AddrRelative16(addr) => writeln!(
            w,
            ".reloc.i16 0x{:04x} {}@{:02x}:{:04x}",
            relocation.info.offset, relocation.source, addr.bank, addr.addr
          )?,
          RelocationType::AddrRelative8(addr) => writeln!(
            w,
            ".reloc.i8 0x{:04x} {}@{:02x}:{:04x}",
            relocation.info.offset, relocation.source, addr.bank, addr.addr
          )?,
        }
      }
    }

    Ok(())
  }
}

/// A block of assembled data.
///
/// A `Block` is a chunk of assmbled data, potentially requiring relocations
/// to be complete. Each `Block` roughly corresponds to an `.origin` directive.
///
/// Because SNASM does not allow the program counter to overflow the end of a 
/// block, `Block` offsets can be assumed to be 16-bit.
#[derive(Debug)]
pub struct Block<'asm> {
  start: u24,
  data: Vec<u8>,
  offsets: Vec<Offset>,
  relocations: Vec<Relocation<'asm>>,
}

/// An "offset" within a [`Block`], describing whether it contains code or some
/// kind of data.
///
/// [`Block`]: struct.Block.html
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[derive(Deserialize, Serialize)]
pub struct Offset {
  /// The data offset that this `Offset` begins at.
  pub start: u16,
  /// The type of this `Offset`.
  pub ty: OffsetType,
}

/// A type of [`Offset`], indicating whether it was declared as code or data.
///
/// [`Offset`]: struct.Offset.html
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[derive(Deserialize, Serialize)]
pub enum OffsetType {
  /// Indicates an offset that was defined as processor instructions.
  Code,
  /// Indicates an offset that was defined as data.
  Data,
}

impl<'asm> Block<'asm> {
  /// Creates a new, empty `Block`.
  pub fn new(start: u24) -> Self {
    Block {
      start,
      data: Vec::new(),
      offsets: Vec::new(),
      relocations: Vec::new(),
    }
  }

  /// Returns a reference to this block's data.
  pub fn data(&self) -> &[u8] {
    &self.data
  }

  /// Returns a mutable reference to this block's data.
  pub fn data_mut(&mut self) -> &mut [u8] {
    &mut self.data
  }

  /// Begins a new `Offset`.
  ///
  /// Returning a sink to write data to.
  pub fn begin_offset<'a>(&'a mut self, ty: OffsetType) -> impl io::Write + 'a {
    self.offsets.push(Offset {
      start: self.data.len() as u16,
      ty,
    });
    &mut self.data
  }

  /// Creates a new `Offset` filled with zeroes.
  ///
  /// Returns the zeroed offset.
  pub fn zeroed_offset(&mut self, ty: OffsetType, len: usize) -> &mut [u8] {
    self.offsets.push(Offset {
      start: self.data.len() as u16,
      ty,
    });
    let old_len = self.data.len();
    let new_len = old_len + len;  
    self.data.resize(new_len, 0);
    &mut self.data[old_len..new_len]
  }

  /// Returns the length of this block.
  pub fn len(&self) -> usize {
    self.data.len()
  }

  /// Adds a new relocation to this block.
  pub fn add_relocation(&mut self, reloc: Relocation<'asm>) {
    self.relocations.push(reloc);
  }

  /// Returns an iterator over all relocations for this block.
  pub fn relocations(&self) -> impl Iterator<Item = &Relocation<'asm>> {
    self.relocations.iter()
  }

  /// Resolves the given relocation, using the given absolute address.
  ///
  /// Returns `false` if a symbol was too far for a pc-relative jump to work.
  pub fn resolve_relocation(
    &mut self,
    relocation: RelocationInfo,
    value: u24,
  ) -> Result<(), RelocationError> {
    let value = match relocation.ty {
      RelocationType::Absolute => Int::I24(value),
      RelocationType::BankRelative(bank) => {
        if bank == value.bank {
          Int::I16(value.addr)
        } else {
          return Err(RelocationError::WrongBank {
            expected: bank,
            got: value.bank,
          });
        }
      }
      RelocationType::AddrRelative16(address) => {
        if address.bank != value.bank {
          return Err(RelocationError::WrongBank {
            expected: address.bank,
            got: value.bank,
          });
        }

        Int::I16(value.addr.wrapping_sub(address.addr))
      }
      RelocationType::AddrRelative8(address) => {
        if address.bank != value.bank {
          return Err(RelocationError::WrongBank {
            expected: address.bank,
            got: value.bank,
          });
        }

        let offset = value.addr.wrapping_sub(address.addr);
        let offset: i8 = match (offset as i16).try_into() {
          Ok(offset) => offset,
          _ => return Err(RelocationError::SymbolTooFar),
        };
        Int::I8(offset as u8)
      }
    };

    value
      .write_le(&mut self.data[relocation.offset as usize..])
      .expect("the space being overwritten should already be zeroed");
    Ok(())
  }
}

/// An error occuring while relocating a symbol.
#[derive(Debug)]
pub enum RelocationError {
  /// Indicates that the symbol's address was not in the expected bank.
  WrongBank {
    /// The bank we wanted.
    expected: u8,
    /// The bank we got.
    got: u8,
  },
  /// Indicates that a symbol was too far; that is, a symbol wasn't actually
  /// within a byte offset range from the `relative_to` field.
  SymbolTooFar,
}

/// A relocation for a missing symbol.
///
/// A `Relocation` describes information that's missing from an assembled
/// `Block`, which can be filled in by a linker.
#[derive(Copy, Clone, Debug)]
pub struct Relocation<'asm> {
  /// Information for resolving the relocation.
  pub info: RelocationInfo,
  /// The symbol that is needed to resolve this relocation.
  pub source: Symbol<'asm>,
}

/// Information describing where a relocation is, and what conditions are
/// necessary to resolve it.
#[derive(Copy, Clone, Debug)]
pub struct RelocationInfo {
  /// An offset into the containing block poing to the exact place where the
  /// symbol value needs to be written.
  pub offset: u16,
  /// The relocation type, which describes how many bytes must be written.
  pub ty: RelocationType,
}

/// A type of a relocation.
///
/// A `RelocationType` describes how large the relocation is and what
/// information can be used to compress the symbol's address.
#[derive(Copy, Clone, Debug)]
pub enum RelocationType {
  /// An absolute, 24-bit relocation. No checks necessary.
  Absolute,
  /// A bank-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the given value.
  ///
  /// This type of relocation is useful for most 16-bit addressing modes.
  BankRelative(u8),
  /// An address-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the bank of the given address. In addition, the lower 16 bits of the
  /// address will be subtracted from those of the symbol, forming a relative
  /// offset.
  ///
  /// This type of relocation is useful for 16-bit branches.
  AddrRelative16(u24),
  /// An address-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the bank of the given address. In addition, the lower 16 bits of the
  /// address will be subtracted from those of the symbol, forming a relative
  /// offset. In addition, this relative offset must be convertible from `i16`
  /// to `i8` without loss of precision.
  ///
  /// This type of relocation is useful for 16-bit branches.
  AddrRelative8(u24),
}
