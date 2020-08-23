//! Blocks of data within an object file.

use std::collections::BTreeMap;
use std::io;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::Range;
use std::ops::RangeFrom;
use std::ops::RangeFull;
use std::ops::RangeInclusive;
use std::ops::RangeTo;
use std::ops::RangeToInclusive;

use crate::int::u24;
use crate::obj::dbg;
use crate::obj::Relocation;

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
  pub(in crate::obj) labels: BTreeMap<u16, Vec<dbg::Label>>,
  pub(in crate::obj) offsets: Vec<dbg::Offset>,
  relocations: Vec<Relocation<'asm>>,
}

impl<'asm> Block<'asm> {
  /// Creates a new, empty `Block`.
  pub fn new(start: u24) -> Self {
    Block {
      start,
      data: Vec::new(),
      labels: BTreeMap::new(),
      offsets: Vec::new(),
      relocations: Vec::new(),
    }
  }

  /// Returns the starting address of this block.
  pub fn start(&self) -> u24 {
    self.start
  }

  /// Returns this block's length, which always fits in 16 bits.
  pub fn len(&self) -> u16 {
    let len = self.data.len();
    debug_assert!(len < u16::MAX as usize);
    len as u16
  }

  /// Begins a new `Offset`.
  ///
  /// Returning a sink to write data to.
  pub fn begin_offset<'a>(
    &'a mut self,
    ty: dbg::OffsetType,
  ) -> OffsetWriter<'a, 'asm> {
    let len = self.len();
    OffsetWriter {
      block: self,
      start: len,
      ty,
    }
  }

  /// Creates a new `Offset` filled with zeroes.
  ///
  /// Returns the zeroed offset.
  pub fn zeroed_offset(&mut self, ty: dbg::OffsetType, len: u16) -> &mut [u8] {
    let old_len = self.len();
    let new_len = old_len + len;

    self.offsets.push(dbg::Offset {
      start: old_len,
      len,
      ty,
    });
    self.data.resize(new_len as usize, 0);
    &mut self[old_len..new_len]
  }

  /// Returns an iterator over all `Offset`s for this block.
  pub fn offsets(&self) -> impl Iterator<Item = &dbg::Offset> {
    self.offsets.iter()
  }

  /// Adds a new `Label` to this block, at the location where more data would
  /// be written.
  pub fn add_label(&mut self, label: dbg::Label) {
    self.add_label_at(label, self.len())
  }

  /// Adds a new `Label` at the given location to this block.
  pub fn add_label_at(&mut self, label: dbg::Label, offset: u16) {
    self.labels.entry(offset).or_insert(Vec::new()).push(label)
  }

  /// Returns an iterator over all `Labels` at the given block offset.
  pub fn labels_at(&self, offset: u16) -> impl Iterator<Item = &dbg::Label> {
    self.labels.get(&offset).map(Vec::as_slice).unwrap_or(&[][..]).iter()
  }

  /// Returns an iterator over all `Label`s for this block.
  pub fn labels(&self) -> impl Iterator<Item = (u16, &dbg::Label)> {
    self.labels.iter().flat_map(|(k, v)| v.iter().map(move |v| (*k, v)))
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

/// `Write` implementation returned by `begin_offset()`.
pub struct OffsetWriter<'a, 'asm>
where
  'asm: 'a,
{
  block: &'a mut Block<'asm>,
  start: u16,
  ty: dbg::OffsetType,
}

impl io::Write for OffsetWriter<'_, '_> {
  #[inline]
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    if buf.len() + self.block.len() as usize > u16::MAX as usize {
      return Err(io::Error::new(io::ErrorKind::Other, "out of space"));
    }
    self.block.data.write(buf)
  }
  #[inline]
  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
    if buf.len() + self.block.len() as usize > u16::MAX as usize {
      return Err(io::Error::new(io::ErrorKind::Other, "out of space"));
    }
    self.block.data.write_all(buf)
  }
  #[inline]
  fn flush(&mut self) -> io::Result<()> {
    self.block.data.flush()
  }
}

impl Drop for OffsetWriter<'_, '_> {
  fn drop(&mut self) {
    let offset = dbg::Offset {
      start: self.start,
      len: self.block.len() - self.start,
      ty: self.ty,
    };
    self.block.offsets.push(offset);
  }
}

impl Index<u16> for Block<'_> {
  type Output = u8;
  #[inline]
  fn index(&self, index: u16) -> &u8 {
    &self.data[index as usize]
  }
}

impl IndexMut<u16> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, index: u16) -> &mut u8 {
    &mut self.data[index as usize]
  }
}

impl Index<Range<u16>> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, Range { start, end }: Range<u16>) -> &[u8] {
    &self.data[start as usize..end as usize]
  }
}

impl IndexMut<Range<u16>> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, Range { start, end }: Range<u16>) -> &mut [u8] {
    &mut self.data[start as usize..end as usize]
  }
}

impl Index<RangeInclusive<u16>> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, range: RangeInclusive<u16>) -> &[u8] {
    let (start, end) = range.into_inner();
    &self.data[start as usize..=end as usize]
  }
}

impl IndexMut<RangeInclusive<u16>> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, range: RangeInclusive<u16>) -> &mut [u8] {
    let (start, end) = range.into_inner();
    &mut self.data[start as usize..=end as usize]
  }
}

impl Index<RangeFrom<u16>> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, RangeFrom { start }: RangeFrom<u16>) -> &[u8] {
    &self.data[start as usize..]
  }
}

impl IndexMut<RangeFrom<u16>> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, RangeFrom { start }: RangeFrom<u16>) -> &mut [u8] {
    &mut self.data[start as usize..]
  }
}

impl Index<RangeTo<u16>> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, RangeTo { end }: RangeTo<u16>) -> &[u8] {
    &self.data[..end as usize]
  }
}

impl IndexMut<RangeTo<u16>> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, RangeTo { end }: RangeTo<u16>) -> &mut [u8] {
    &mut self.data[..end as usize]
  }
}

impl Index<RangeToInclusive<u16>> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, RangeToInclusive { end }: RangeToInclusive<u16>) -> &[u8] {
    &self.data[..=end as usize]
  }
}

impl IndexMut<RangeToInclusive<u16>> for Block<'_> {
  #[inline]
  fn index_mut(
    &mut self,
    RangeToInclusive { end }: RangeToInclusive<u16>,
  ) -> &mut [u8] {
    &mut self.data[..=end as usize]
  }
}

impl Index<RangeFull> for Block<'_> {
  type Output = [u8];
  #[inline]
  fn index(&self, _: RangeFull) -> &[u8] {
    &self.data[..]
  }
}

impl IndexMut<RangeFull> for Block<'_> {
  #[inline]
  fn index_mut(&mut self, _: RangeFull) -> &mut [u8] {
    &mut self.data[..]
  }
}
