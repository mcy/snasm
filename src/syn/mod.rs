//! SNASM's 65816 assembly syntax.
//!
//! This module provides a parser for a faithful AST representation of
//! SNASM's variant of 65816 syntax.
//!
//! Throughout this module, the `'asm` lifetime referrs to the lifetime of the
//! file's text.
//!
//! # Syntax
//! SNASM's syntax is, at the top level, described in terms of *atoms*. An atom
//! is a single command for the assembler, be it a label, a directive, or a
//! 65816 instruction. (The parser also parses empty lines as atoms.)
//!
//! Comments begin with a semicolon (`;`) and end with a newline.
//! The parser will preserve comments.
//!
//! ## Operands
//!
//! SNASM symbols can be any combination of letters, digits, periods, and
//! underscores, though they cannot begin with a digit. `.l1234`,
//! `physics.get_pos`, and `my_cool_fn123` are all valid symbols.
//!
//! SNASM integers may be decimal, binary, or hexadecimal: `123`, `%1010`, or
//! `$99beef`. They may also be interspersed with underscores in any position,
//! other than the first character. Decimal literals may also be negative:
//! `-55`. This is a shorthand for the two's complement of that decimal integer.
//!
//! The type of an integer is the smallest of `i8`, `i16`, and `i24` that can
//! faithfully represent it. Negative integers have a smaller range, since the
//! sign bit needs to be stored somewhere. The type can be specified with a
//! prefix: for example, `$ffu16` is the 16-bit integer `0x00ff`. All integers
//! are two's complement, little-endian.
//!
//! Additionally, forward and backwards numeric label references, like `1f` and
//! `2b`, are valid operands.
//!
//! Eventually, SNASM will support ASCII string literals.
//!
//! ## Labels
//! A label is a named position in a program. A label can either be for the form
//! `<symbol>:` or `<digit>:`. For the former, this introduces a symbol with the
//! name `<symbol>`, while the latter may be referred to with `<digit>b` or
//! `<digit>f`. For example, `1f` represents the *next* label `1:` occuring in
//! the program, while `1b` the *previous*.
//!
//! ## Directives
//! A directive begins with a symbol starting with a period, like `.origin`,
//! followed by a number of comma-separated operands.
//! Directives affect assembler state in some way: `.origin <pc>` sets the
//! program counter, while `.zero <n>` inserts `n` zeroes into the program.
//!
//! TODO(mcyoung): Document all directives.
//!
//! ## Instructions
//! Instructions are literal 65816 instructions. An instruction is a
//! case-insensitive, three character mnemonic, like `adc` or `tax`, followed
//! by one of the following generic addressing modes:
//! - Accumulator: `a`.
//! - Immediate: `#<operand>`.
//! - Absolute: `<operand>`.
//! - Indirect: `(<operand>)`.
//! - Indexed absolute: `<operand>, <reg>`.
//! - Pre-indexed indirect: `(<operand>, <reg>)`.
//! - Post-indexed indirect: `(<operand>), <reg>`.
//! - Bi-indexed indirect: `(<operand>, <reg>), <reg>`.
//! - Long indirect: `[<operand>]`.
//! - Long post-indexed indirect: `[<operand>], <reg>`.
//!
//! `<operand>` is any operand expression, while `<reg>` is any of the `x`, `y`,
//! or `s` registers. For example:
//! ```text
//! adc $1235, x
//! lda #$100u16
//! asl a
//! jml [$f0_f0_f0]
//! ```
//!
//! Additionally, an instruction may be followed by a suffix to indicate its
//! length: for example, `lda.i8 my_label` will always be interpreted as the
//! lowest byte of `my_label`.
//!
//! The parser is not aware of what the valid combinations of mnemonics,
//! addressing modes, index registers, and operand types are.

use crate::isa::Mnemonic;

pub mod fmt;
mod parse;

pub use fmt::print;
pub use parse::{parse, Error, Position, Span};

/// A symbol, representing some location in a program.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol<'asm> {
  /// The name of this symbol.
  pub name: &'asm str,
}

/// A line comment in a file.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Comment<'asm> {
  /// The text of the comment, including the comment character.
  ///
  /// E.g., `"; This is a function."`.
  pub text: &'asm str,
}

/// An assembly file.
///
/// An assembly file consists of several
#[derive(Clone, Debug)]
pub struct File<'asm> {
  /// The name of this file.
  pub name: Option<&'asm str>,
  /// The atoms that make up this file.
  pub atoms: Vec<Atom<'asm>>,
}

/// A span with a file name attached to it.
#[derive(Clone)]
pub struct FileSpan<'asm> {
  /// The name of the file.
  pub name: Option<&'asm str>,
  /// A span within the file.
  pub span: Span<'asm>,
}

impl std::fmt::Debug for FileSpan<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    match &self.name {
      Some(name) => {
        write!(f, "{:?}[{}, {}]", name, self.span.start(), self.span.end())
      }
      None => write!(f, "<?>[{}, {}]", self.span.start(), self.span.end()),
    }
  }
}

/// A syntactic atom.
///
/// An atom describes a "complete" assembler command, such as a label, a
/// directive such as `.origin`, or an actual instruction.
#[derive(Clone, Debug)]
pub struct Atom<'asm> {
  /// The actual semantic content of the atom.
  inner: AtomType<'asm>,
  /// This atom's end-of-line comment, if it had one.
  comment: Option<Comment<'asm>>,
  /// Whether this atom was the last one on a line.
  has_newline: bool,
  /// The span this atom was parsed from, if any.
  span: Option<FileSpan<'asm>>,
}

/// Various types of `Atom`s.
#[derive(Clone, Debug)]
pub enum AtomType<'asm> {
  /// A label definition: `foo:`.
  Label(Symbol<'asm>),

  /// A local digit label definition: `1:`.
  DigitLabel(u8),

  /// A directive: `.origin $100`.
  Directive(Symbol<'asm>, Vec<Operand<'asm>>),

  /// An instruction: `adc $ff, x`.
  ///
  /// Each instruction consists of a mnemonic, an optional width, and an
  /// optional address expression.
  Instruction(Mnemonic, Option<IntType>, Option<AddrExpr<Operand<'asm>>>),

  /// An empty atom, representing an empty line.
  Empty,
}

/// An operand, which can be used with a directive or an instruction.
#[derive(Clone, Debug)]
pub enum Operand<'asm> {
  /// A literal integer operand.
  Int(Int),
  /// A string operand.
  String(&'asm str),
  /// A symbol operand, which needs to be resolved against the symbol
  /// table.
  Symbol(Symbol<'asm>),
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
      "i8" | "I8" => Some(Self::I8),
      "i16" | "I16" => Some(Self::I16),
      "i24" | "I24" => Some(Self::I24),
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
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum AddrExpr<Arg> {
  /// Accumulator addressing: `xyz a`.
  Acc,
  /// Immediate addressing: `xyz #$ff`.
  Imm(Arg),
  /// Absolute addressing: `xyz $ff`.
  Abs(Arg),
  /// Indexed addressing: `xyz $ff, x`.
  Idx(Arg, IdxReg),
  /// Indirect addressing: `xyz ($ff)`.
  Ind(Arg),
  /// Indxed indirect addressing: `xyz ($ff, x)`
  IdxInd(Arg, IdxReg),
  /// Indirect indexed addressing: `xyz ($ff), y`.
  IndIdx(Arg, IdxReg),
  /// Indexed indirect indexed addressing: `xyz ($ff, s), y`
  IdxIndIdx(Arg, IdxReg, IdxReg),
  /// Long indirect addressing: `xyz [$ff]`.
  LongInd(Arg),
  /// Long indirect indexed addressing: `xyz [$ff], y`.
  LongIndIdx(Arg, IdxReg),
  /// Move addressing: `xyz $aa, $bb`.
  Move(Arg, Arg),
}

impl<Arg> AddrExpr<Arg> {
  /// Returns references to this addressing expression's arguments.
  ///
  /// Addressing modes have varying numbers of arguments. This function returns
  /// at most two arguments, but most addressing modes have less than that.
  pub fn args(&self) -> (Option<&Arg>, Option<&Arg>) {
    match self {
      Self::Acc => (None, None),
      Self::Imm(a) => (Some(a), None),
      Self::Abs(a) => (Some(a), None),
      Self::Idx(a, _) => (Some(a), None),
      Self::Ind(a) => (Some(a), None),
      Self::IdxInd(a, _) => (Some(a), None),
      Self::IndIdx(a, _) => (Some(a), None),
      Self::IdxIndIdx(a, _, _) => (Some(a), None),
      Self::LongInd(a) => (Some(a), None),
      Self::LongIndIdx(a, _) => (Some(a), None),
      Self::Move(a, b) => (Some(a), Some(b)),
    }
  }
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