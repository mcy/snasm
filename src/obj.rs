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
use std::io;

use crate::int::u24;
use crate::int::Width;
use crate::isa::Instruction;
use crate::syn::fmt;
use crate::syn::operand::Symbol;

/// An assembled object file.
///
/// An `Object` is made up of a collection of `Block`s, each of which starts at
/// a different 24-bit address.
#[derive(Debug)]
pub struct Object<'asm> {
  name: Option<&'asm str>,
  blocks: HashMap<u24, Block<'asm>>,
  globals: Vec<(Symbol<'asm>, u24)>,
}

impl<'asm> Object<'asm> {
  /// Creates a new, empty `Object`.
  pub fn new(name: Option<&'asm str>) -> Self {
    Object {
      name,
      blocks: HashMap::new(),
      globals: Vec::new(),
    }
  }

  /// Returns the name of this object, if any.
  ///
  /// This is the same as the name of the file that the object was assembled
  /// from.
  pub fn name(&self) -> Option<&'asm str> {
    self.name
  }

  /// Creates a new, empty block at the given starting address.
  pub fn new_block(&mut self, start: u24) {
    self.blocks.insert(start, Block::new());
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
    for (addr, block) in &self.blocks {
      writeln!(w, ".origin 0x{:06x}", addr)?;
      for i in 0..block.offsets.len() {
        let (start, ty) = block.offsets[i];
        let end = block
          .offsets
          .get(i + 1)
          .map(|(idx, _)| idx)
          .copied()
          .unwrap_or(block.data.len());

        match ty {
          OffsetType::Code => {
            write!(w, "{:06x}:", addr.to_u32() + start as u32)?;
            for j in start..end {
              write!(w, "  {:02x}", block.data[j])?;
            }

            let expected_len = (end - start) * 4;
            let padding = 16 - expected_len;
            for _ in 0..padding {
              write!(w, " ")?;
            }
            if let Ok(instruction) = Instruction::read(&block.data[start..]) {
              fmt::print_instruction(
                fmt::Options::default(),
                instruction,
                &mut w,
              )?
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
          }
        }
        writeln!(w, "")?;
      }

      for relocation in &block.relocations {
        writeln!(
          w,
          ".reloc.{} 0x{:04x} {}",
          relocation.destination_width,
          relocation.instruction_offset,
          relocation.source
        )?;
      }
      writeln!(w, "")?;
    }

    Ok(())
  }
}

/// A block of assembled data.
///
/// A `Block` is a chunk of assmbled data, potentially requiring relocations
/// to be complete. Each `Block` roughly corresponds to an `.origin` directive.
#[derive(Debug)]
pub struct Block<'asm> {
  data: Vec<u8>,
  offsets: Vec<(usize, OffsetType)>,
  relocations: Vec<Relocation<'asm>>,
}
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum OffsetType {
  Code,
  Data,
}

impl<'asm> Block<'asm> {
  /// Creates a new, empty `Block`.
  pub fn new() -> Self {
    Block {
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

  /// Begins a new code offset, returning a sink to write the new instruction
  /// to.
  pub fn begin_code_offset<'a>(&'a mut self) -> impl io::Write + 'a {
    self.offsets.push((self.data.len(), OffsetType::Code));
    &mut self.data
  }

  /// Begins a new data offset, returning a sink to write the new data to.
  pub fn begin_data_offset<'a>(&'a mut self) -> impl io::Write + 'a {
    self.offsets.push((self.data.len(), OffsetType::Data));
    &mut self.data
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
}

/// A relocation for a missing symbol.
///
/// A `Relocation` describes information that's missing from an assembled
/// `Block`, which can be filled in by a linker.
#[derive(Debug)]
pub struct Relocation<'asm> {
  /// An offset into the containing block indicating where the instruction
  /// targeted by this relocation is located.
  pub instruction_offset: u16,
  /// An offset into the containing block poing to the exact place where the
  /// symbol value needs to be written.
  pub destination_offset: u16,
  /// The width of the destination: how many bytes need to be actually written.
  pub destination_width: Width,
  /// The symbol that is needed to resolve this relocation.
  pub source: Symbol<'asm>,
}
