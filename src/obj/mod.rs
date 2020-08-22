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
use std::path::Path;

use crate::int::u24;
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
  #[inline]
  pub fn dump(&self, w: impl io::Write) -> io::Result<()> {
    dump::dump(self, w)
  }
}
