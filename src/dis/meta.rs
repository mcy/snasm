//! ROM metadata, which describe how to disassemble a ROM into source files.

use crate::int::u24;

pub struct Metadata {
  pub files: Vec<Files>,
}

pub struct File {
  pub name: String,
  pub regions: Vec<Region>,
}

pub struct Region {
  pub rom_start: u24,
  pub mem_start: u24,
  pub len: u16,
}