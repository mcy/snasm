//! SNASM's 65816 assembly syntax.
//!
//! This module provides a parser for a faithful AST representation of
//! SNASM's variant of 65816 syntax.
//!
//! Throughout this module, the `'asm` lifetime referrs to the lifetime of the
//! file's text.

#[macro_use]
pub mod fmt;

pub mod atom;
pub mod code;
pub mod int;
pub mod operand;
pub mod src;

mod parse;
