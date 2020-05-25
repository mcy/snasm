//! 65816 assembly syntax.
//!
//! This module provides a parser for a faithful AST representation of
//! SNASM's variant of 65816 syntax.
//!
//! TODO(mcyoung): describe the syntax.

use crate::isa::Mnemonic;

pub mod fmt;
mod parse;

pub use fmt::print;
pub use parse::{parse, Error};

/// A symbol, representing some location in a program.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol {
  /// The name of this symbol.
  pub name: String,
}

/// A line comment in a file.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Comment {
  /// The text of the comment, including the comment character.
  ///
  /// E.g., `"; This is a function."`.
  pub text: String,
}

/// An assembly file.
///
/// An assembly file consists of several
#[derive(Clone, Debug)]
pub struct File {
  name: String,
  atoms: Vec<Atom>,
}

/// A syntactic atom.
///
/// An atom describes a "complete" assembler command, such as a label, a
/// directive such as `.origin`, or an actual instruction.
#[derive(Clone, Debug)]
pub struct Atom {
  /// The actual semantic content of the atom.
  inner: AtomType,
  /// This atom's end-of-line comment, if it had one.
  comment: Option<Comment>,
  /// Wether this
  has_newline: bool,
}

/// Various types of `Atom`s.
#[derive(Clone, Debug)]
pub enum AtomType {
  /// A label definition: `foo:`.
  Label {
    /// The symbol introduced by the label.
    name: Symbol,
  },

  /// A directive: `.origin $100`.
  Directive {
    /// The name of the directive, including the leading period.
    name: Symbol,
    /// The arguments for the directive.
    args: Vec<Operand>,
  },

  /// An instruction: `adc $ff, x`.
  Instruction {
    /// The instruction's mnemonic.
    mne: Mnemonic,
    /// An optional "address expression", describing a potential addressing
    /// mode.
    expr: Option<AddrExpr>,
  },

  /// An empty atom, representing an empty line.
  Empty,
}

/// An operand, which can be used with a directive or an instruction.
#[derive(Clone, Debug)]
pub enum Operand {
  /// A literal integer operand.
  Int(Int),
  /// A string operand.
  String(String),
  /// A symbol operand, which needs to be resolved against the symbol
  /// table.
  Symbol(Symbol),
  /// A numeric label reference, like `1f` or `2b`.
  LabelRef {
    /// The integer value of this reference, between `0` and `9`.
    value: u8,
    /// Whether this is a forward reference or a backward reference.
    is_forward: bool,
  },
}

/// An integer literal.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Int {
  /// The value of this integer. If negative, it will be fully sign-extended,
  /// though only the portion specified by `ty` should be used. In particularm
  /// 0xffffffff and 0x0000ffff represent the same two-byte integer, though
  /// the former is viewed as coming from a "signed" literal.
  pub value: i32,
  /// The "style" of this integer, i.e, the base it was parsed in.
  pub style: DigitStyle,
  /// The type (i.e., width) of this integer.
  pub ty: IntType,
}

impl Int {
  /// Returns whether this Int is "negative", by observing the sign bit of the
  /// underlying `i32` value.
  pub fn is_negative(self) -> bool {
    self.value < 0
  }
}

/// A digit style: decimal, hex, or binary.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum DigitStyle {
  /// Decimal style: `123`.
  Dec,
  /// Hex style: `$dead`.
  Hex,
  /// Binary style: `%0110`.
  Bin,
}

impl DigitStyle {
  /// Returns this `DigitStyle`'s associated radix.
  pub fn radix(self) -> u32 {
    match self {
      Self::Dec => 10,
      Self::Hex => 16,
      Self::Bin => 2,
    }
  }
}

/// An integer type: a one, two, or three-byte integers.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum IntType {
  /// A single byte.
  I8,
  /// A two-byte word.
  I16,
  /// A three-byte long.
  I24,
}

impl IntType {
  /// Parses a string into an `IntType`.
  pub fn from_str(s: &str) -> Option<Self> {
    match s {
      "i8" => Some(Self::I8),
      "i16" => Some(Self::I16),
      "i24" => Some(Self::I24),
      _ => None,
    }
  }

  /// Returns the smallest unsigned `IntType` that fits `val`, if such exists.
  ///
  /// Positive numbers are treated as unsigned; negative numbers, however, are
  /// reated as signed, and so will require an extra bit for the sign bit.
  /// Negative numbers are simply treated as alternate representations for
  /// positive, unsigned numbers. When in doubt, stick add an explicit prefix.
  pub fn smallest_for(val: i32) -> Option<Self> {
    #[allow(overlapping_patterns)]
    match val {
      0..=0xff => Some(Self::I8),
      0..=0xffff => Some(Self::I16),
      0..=0xffffff => Some(Self::I24),
      -0x80..=0 => Some(Self::I8),
      -0x8000..=0 => Some(Self::I16),
      -0x800000..=0 => Some(Self::I24),
      _ => None,
    }
  }
}

/// A "address expression", encompassing all of the syntactic variations
/// shared by the 65816 addressing modes.
#[derive(Clone, Debug)]
pub enum AddrExpr {
  /// Accumulator addressing: `xyz a`.
  Acc,
  /// Immediate addressing: `xyz #$ff`.
  Imm(Operand),
  /// Absolute addressing: `xyz $ff`.
  Abs(Operand),
  /// Indexed addressing: `xyz $ff, x`.
  Idx(Operand, IdxReg),
  /// Indirect addressing: `xyz ($ff)`.
  Ind(Operand),
  /// Indxed indirect addressing: `xyz ($ff, x)`
  IdxInd(Operand, IdxReg),
  /// Indirect indexed addressing: `xyz ($ff), y`.
  IndIdx(Operand, IdxReg),
  /// Indexed indirect indexed addressing: `xyz ($ff, s), y`
  IdxIndIdx(Operand, IdxReg, IdxReg),
  /// Long indirect addressing: `xyz [$ff]`.
  LongInd(Operand),
  /// Long indirect indexed addressing: `xyz [$ff], y`.
  LongIndIdx(Operand, IdxReg),
}

/// A register that can be used in "index position".
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum IdxReg {
  /// The `x` register.
  X,
  /// The `y` register.
  Y,
  /// The `s` register.
  S,
}

impl IdxReg {
  /// Parse an `IdxReg` from a string.
  pub fn from_str(s: &str) -> Option<Self> {
    match s {
      "x" | "X" => Some(Self::X),
      "y" | "Y" => Some(Self::Y),
      "s" | "S" => Some(Self::S),
      _ => None,
    }
  }

  /// Returns the name for this `IdxReg`.
  pub fn name(self) -> &'static str {
    match self {
      Self::X => "x",
      Self::Y => "y",
      Self::S => "s",
    }
  }
}

/// Represents a either a symbol referring to some location in a program,
/// or an immediate value of type `T`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SymOr<T> {
  /// A pending symbol.
  Sym(String),
  /// An immediate, here and now.
  Imm(T),
}

impl<T> SymOr<T> {
  /// Resolves a symbol by replacing `self` with an Imm variant.
  pub fn resolve(&mut self, imm: T) {
    *self = Self::Imm(imm);
  }
}
