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
  bank: u8,
  /// A 16-bit address within a bank.
  addr: u16,
}
