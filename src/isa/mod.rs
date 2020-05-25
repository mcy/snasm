//! The 65816 instruction set architecture, the ISA that the SNES's processor
//! implements.
//!
//! This module provides functions for assembling, disassembling, and
//! manipulating machine code for the 65816.

pub mod addressing;
mod instruction;
mod mnemonic;

pub use addressing::AddrMode;
pub use instruction::Instruction;
pub use mnemonic::Mnemonic;

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
}
