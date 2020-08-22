//! ROM metadata, which describe how to disassemble a ROM into source files.

use std::path::PathBuf;

use serde::Deserialize;
use serde::Serialize;

use crate::obj::Offset;
use crate::int::u24;

#[derive(Deserialize, Serialize)]
pub struct Metadata {
  pub files: Vec<File>,
}

#[derive(Deserialize, Serialize)]
pub struct File {
  pub name: PathBuf,
  pub blocks: Vec<Block>,
}

#[derive(Deserialize, Serialize)]
pub struct Block {
  pub start: u24,
  pub len: u16,
  pub offsets: Vec<Offset>,
}