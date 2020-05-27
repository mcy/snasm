//! The 65816 instruction set architecture, the ISA that the SNES's processor
//! implements.
//!
//! This module provides functions for assembling, disassembling, and
//! manipulating machine code for the 65816.

mod instruction;
mod mnemonic;

pub use instruction::Instruction;
pub use mnemonic::Mnemonic;
