//! The SNASM object file format.
//!
//! A SNASM object consists of a set of *blocks*, which contain a mixture of
//! data and code. Each block has a designated starting address in ROM.
//! Each block may define a number of relocations, describing to the linker
//! what information is missing to link this object into a ROM.
//!
//! Additionally, each object advertises a list of global symbols for use by the
//! linker.

use std::collections::BTreeMap;
use std::collections::HashSet;
use std::io;
use std::path::Path;

use crate::int::u24;
use crate::rom::Rom;
use crate::syn::operand::Symbol;

mod block;
mod dump;
mod relo;

pub use block::*;
pub use relo::*;

pub mod dbg;

/// An assembled object file.
///
/// An `Object` is made up of a collection of `Block`s, each of which starts at
/// a different 24-bit address.
#[derive(Debug)]
pub struct Object<'asm> {
  name: &'asm Path,
  blocks: BTreeMap<u24, Block<'asm>>,
  globals: Vec<(Symbol<'asm>, u24)>,
}

impl<'asm> Object<'asm> {
  /// Creates a new, empty `Object`.
  pub fn new(name: &'asm (impl AsRef<Path> + ?Sized)) -> Self {
    Object {
      name: name.as_ref(),
      blocks: BTreeMap::new(),
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
  #[inline]
  pub fn dump(&self, w: impl io::Write) -> io::Result<()> {
    dump::dump(self, w)
  }

  /// Creates a new object by reading `rom` using the instructions in `debug`.
  pub fn from_debug_info(
    rom: &dyn Rom,
    debug: &'asm dbg::File,
  ) -> Object<'asm> {
    let mut object = Object::new(&debug.name);
    for region in &debug.blocks {
      let block = object.new_block(region.start);
      for offset in &region.offsets {
        let bytes = block.zeroed_offset(offset.ty, offset.len);
        rom
          .read(region.start.offset(offset.start as i16), bytes)
          .expect("this error should be handled gracefully");
      }
    }
    object
  }

  /// Simplifies debug information, ensuring that it is minimal and internally
  /// consistent.
  ///
  /// This function may be expensive to call, since it sorts and copies internal
  /// buffers.
  pub fn simplify_debug_info(&mut self) {
    for (_, block) in &mut self.blocks {
      // Ensure that the label table's is_global markers match those of the
      // overall object.
      let mut global_set = HashSet::new();
      for (global, _) in &self.globals {
        global_set.insert(global.name);
      }
      for (_, label) in &mut block.labels {
        match label {
          dbg::Label::Symbol(sym) => {
            sym.is_global = global_set.contains(sym.name.as_str())
          }
          _ => {}
        }
      }

      // Re-build the offset table, such that the following properties hold:
      // - No two offsets overlap.
      // - The offsets cover the entire span of self.data (filling in spaces
      //   with data offsets).
      // - No two adjecent offsets have the same type.
      let offsets = &mut block.offsets;
      offsets.sort_by_key(|offset| offset.start);

      let mut new_offsets = Vec::new();
      for i in 0..offsets.len() {
        let mut offset = offsets[i];
        if i == 0 {
          if offset.start != 0 {
            match offset.ty {
              dbg::OffsetType::Code => new_offsets.push(dbg::Offset {
                start: 0,
                len: offset.start,
                ty: dbg::OffsetType::Data,
              }),
              dbg::OffsetType::Data => offset.start = 0,
            }
          }

          new_offsets.push(offset);
          continue;
        }

        let prev = new_offsets.last_mut().unwrap();
        let prev_end = prev.start + prev.len;
        // Fix a pair of overlapping offsets by shortening the previous one.
        if prev.start + prev.len > offset.start {
          prev.len = prev_end - offset.start;
        }
        let prev_end = prev.start + prev.len;

        match (prev.ty, offset.ty) {
          (dbg::OffsetType::Code, dbg::OffsetType::Code)
            if prev_end == offset.start =>
          {
            prev.len += offset.len
          }
          (dbg::OffsetType::Code, dbg::OffsetType::Code) => {
            new_offsets.push(dbg::Offset {
              start: prev_end,
              len: offset.start - prev_end,
              ty: dbg::OffsetType::Data,
            });
            new_offsets.push(offset);
          }
          (dbg::OffsetType::Data, dbg::OffsetType::Data) => {
            prev.len += offset.len
          }
          (dbg::OffsetType::Data, _) => {
            prev.len = offset.start - prev_end;
            new_offsets.push(offset);
          }
          (_, dbg::OffsetType::Data) => {
            offset.start = prev_end;
            new_offsets.push(offset);
          }
        }
      }
      block.offsets = new_offsets;
    }
  }

  /// Copies debug information out of this object into a serializeable format.
  pub fn make_debug_info(&self) -> dbg::File {
    let mut file = dbg::File {
      name: self.file_name().into(),
      blocks: Vec::new(),
    };

    for (_, block) in self.blocks() {
      let block = dbg::Block {
        start: block.start(),
        len: block.len(),
        offsets: block.offsets().cloned().collect(),
        labels: BTreeMap::new(),
      };

      file.blocks.push(block);
    }

    file
  }
}
