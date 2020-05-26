//! The 65816 instruction set architecture, the ISA that the SNES's processor
//! implements.
//!
//! This module provides functions for assembling, disassembling, and
//! manipulating machine code for the 65816.

mod instruction;
mod mnemonic;

pub use instruction::Instruction;
pub use mnemonic::Mnemonic;

/// An "address" of 8, 16, or 24 bits.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Addr {
  /// An 8-bit address.
  I8(u8),
  /// An 16-bit address.
  I16(u16),
  /// An 24-bit address.
  I24(Long),
}

/// A 24-bit absolute address.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Long {
  /// The "bank byte", that is, the top byte of the address determining which
  /// bank it corresponds to.
  pub bank: u8,
  /// A 16-bit address within a bank.
  pub addr: u16,
}

impl Long {
  /// Create a `Long` value out of a `u32`.
  pub fn from_u32(i: u32) -> Self {
    Self {
      bank: (i >> 16) as u8,
      addr: i as u16,
    }
  }

  /// Converts this `Long` into a `u32`, with the top byte cleared.
  pub fn to_u32(self) -> u32 {
    ((self.bank as u32) << 16) | (self.addr as u32)
  }

  /// Offsets this `Long`. This does not perform 24-bit arithmetic. Instead,
  /// only the `addr` part is affected, always wrapping around on overflow.
  pub fn offset(&mut self, offset: i16) {
    self.addr = self.addr.wrapping_add(offset as u16)
  }
}
