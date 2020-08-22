//! Debug information attached to an object file, describing the assembly file
//! it was assembled from.

use std::path::PathBuf;

use serde::Deserialize;
use serde::Serialize;

use crate::int::u24;

/// Overall metadata for a a ROM, as a collection of [`File`]s.
///
/// [`File`]: struct.File.html
#[derive(Deserialize, Serialize)]
pub struct Metadata {
  /// A list of assembly files that a ROM was assembled from.
  pub files: Vec<File>,
}

/// Non-program information associated with an [`Object`], which describes the
/// assembly file it came from.
#[derive(Deserialize, Serialize)]
pub struct File {
  /// The name of the original assembly file.
  pub name: PathBuf,
  /// Blocks within the original object file.
  pub blocks: Vec<Block>,
}

/// A [`Block`] which now only carries it associated metadata, describing where
/// to find its code relative to some ROM.
///
/// [`Block`]: ../struct.Block.html
#[derive(Deserialize, Serialize)]
pub struct Block {
  /// The start of this `Block` as an absolute address.
  pub start: u24,
  /// The length of this `Block`.
  pub len: u16,
  /// `Offset` information within the block.
  pub offsets: Vec<Offset>,
}

/// An "offset" within a [`Block`], describing whether it contains code or some
/// kind of data.
///
/// [`Block`]: ../struct.Block.html
#[derive(Copy, Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
pub struct Offset {
  /// The data offset that this `Offset` begins at.
  pub start: u16,
  /// The length of this `Offset`.
  pub len: u16,
  /// The type of this `Offset`.
  pub ty: OffsetType,
}

/// A type of [`Offset`], indicating whether it was declared as code or data.
///
/// [`Offset`]: ../struct.Offset.html
#[derive(Copy, Clone, PartialEq, Eq, Debug, Deserialize, Serialize)]
pub enum OffsetType {
  /// Indicates an offset that was defined as processor instructions.
  Code,
  /// Indicates an offset that was defined as data.
  Data,
}
