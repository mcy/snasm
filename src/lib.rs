//! SNASM, a SNES assembler/disassembler and patch generation tool.

#![deny(missing_docs)]
#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

pub mod asm;
pub mod error;
pub mod int;
pub mod isa;
pub mod link;
pub mod obj;
pub mod rom;
pub mod syn;
