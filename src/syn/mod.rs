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
//! ## Symbols
//!
//! SNASM symbols can be any combination of letters, digits, periods, and
//! underscores, though they cannot begin with a digit. `.l1234`,
//! `physics.get_pos`, and `my_cool_fn123` are all valid symbols.
//!
//! ## Integers
//!
//! SNASM integers may be decimal, binary, or hexadecimal: `123`, `%1010`, or
//! `$99beef`. They may also be interspersed with underscores in any position,
//! other than the first character.
//!
//! The type of an integer is the smallest of `i8`, `i16`, and `i24` that can
//! faithfully represent the literal. For example, `255` is an `i8`, but `256`
//! is an `i16`.
//!
//! This type can also be forced with a prefix, to force it to a particular
//! length: for example, `$ffi16` is the 16-bit integer `0x00ff`.
//!
//! An integer literal may also be lead by a `-` or a `!`. These indicate the
//! two's complement and one's complement (i.e., binary not), respectively.
//! Note that these operations are applied *after* the type has been determined.
//! SNASM integers are not meaningfully signed or unsigned.
//!
//! ## Labels
//!
//! A label is a named position in a program. A label can either be for the form
//! `<symbol>:` or `<digit>:`. For the former, this introduces a symbol with the
//! name `<symbol>`, while the latter may be referred to with `<digit>b` or
//! `<digit>f`. For example, `1f` represents the *next* label `1:` occuring in
//! the program, while `1b` the *previous*.
//!
//! ## Directives
//!
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
//! jmp [$f0_f0_f0]
//! ```
//!
//! Additionally, an instruction may be followed by a suffix to indicate its
//! length: for example, `lda.i8 my_label` will always be interpreted as the
//! lowest byte of `my_label`.
//!
//! The parser is not aware of what the valid combinations of mnemonics,
//! addressing modes, index registers, and operand types are; those invariants
//! are checked by the assembler proper.
//!
//! ## Integer type-checking
//!
//! SNASM will never implicitly sign/zero-extend, or truncate, any integers.
//! For example, `jmp $12` is invalid, since `$12` has type `i8`, but `jmp`
//! requiores an `i16` or `i24`. `jmp $12_i16` would be accepted as an absolute
//! near-jump.
//!
//! SNASM will also infer the type of addressing mode from the integer type.
//! For example, `adc $12` will always perform a direct-page access, which can
//! be enforced with a suffix: `adc.i8 $12`. Type-mismatches arising from using
//! suffixes are also an error: `adc.i8 $12i16` is not allowed.

use crate::int::Int;
use crate::int::Width;
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
  pub inner: AtomType<'asm>,
  /// This atom's end-of-line comment, if it had one.
  pub comment: Option<Comment<'asm>>,
  /// Whether this atom was the last one on a line.
  pub has_newline: bool,
  /// The span this atom was parsed from, if any.
  pub span: Option<FileSpan<'asm>>,
}

/// Various types of `Atom`s.
#[derive(Clone, Debug)]
pub enum AtomType<'asm> {
  /// A label definition: `foo:`.
  Label(Symbol<'asm>),

  /// A local digit label definition: `1:`.
  DigitLabel(Digit),

  /// A directive: `.origin $100`.
  Directive(Directive<'asm>),

  /// An instruction: `adc $ff, x`.
  ///
  /// Each instruction consists of a mnemonic, an optional width, and an
  /// optional address expression.
  Instruction(InstructionLine<'asm>),

  /// An empty atom, representing an empty line.
  Empty,
}

/// An assembler directive, which may be potentially unknown to the assembler.
#[derive(Clone, Debug)]
pub struct Directive<'asm> {
  /// The original symbol this directive was parsed with.
  pub sym: Symbol<'asm>,
  /// This directive's type.
  pub ty: DirectiveType<'asm>,
}

impl<'asm> Directive<'asm> {
  /// Creates a new `Directive`, detecting known symbol names, such as
  /// ".origin".
  pub fn from_symbol(
    sym: Symbol<'asm>,
    args: Vec<Operand<'asm>>,
  ) -> Option<Self> {
    let ty = match sym.name {
      ".origin" => match &args[..] {
        [Operand::Int(int)] => DirectiveType::Origin(*int),
        _ => return None,
      },
      ".extern" => match &args[..] {
        [Operand::Symbol(sym)] => DirectiveType::Extern {
          sym: *sym,
          bank: None,
        },
        [Operand::Symbol(sym), Operand::Int(bank)] => DirectiveType::Extern {
          sym: *sym,
          bank: Some(*bank),
        },
        _ => return None,
      },
      _ => DirectiveType::Unknown(args),
    };
    Some(Directive { sym, ty })
  }
}

/// A directive type, indicating a (potentially well-known) assembler directive.
#[derive(Clone, Debug)]
pub enum DirectiveType<'asm> {
  /// The `.origin` directive, indicating to the assembler that the program
  /// counter should unconditionally jump to the given argument.
  Origin(IntLit),
  /// The `.extern` directive, which indicates that a name is defined in another
  /// file. If the bank the symbol is allocated in is not given, it is assumed
  /// to be in the current bank.
  Extern {
    /// The external symbol name.
    sym: Symbol<'asm>,
    /// The bank, if different from the current one.
    bank: Option<IntLit>,
  },
  /// A directive unknown to the assembler.
  Unknown(Vec<Operand<'asm>>),
}

/// An unassembled instruction, which may refer to a ficticious instruction.
#[derive(Clone, Debug)]
pub struct InstructionLine<'asm> {
  /// The instruction's mnemonic.
  pub mne: Mnemonic,
  /// A width suffix, like `.i8`.
  pub width: Option<Width>,
  /// The addressing mode and operand for the instruction.
  pub addr: Option<AddrExpr<Operand<'asm>>>,
}

/// An operand, which can be used with a directive or an instruction.
#[derive(Clone, Debug)]
pub enum Operand<'asm> {
  /// A literal integer operand.
  Int(IntLit),
  /// A string operand.
  String(&'asm str),
  /// A symbol operand, which needs to be resolved against the symbol
  /// table.
  Symbol(Symbol<'asm>),
  /// A numeric label reference, like `1f` or `2b`.
  DigitLabelRef(DigitLabelRef),
}

/// A digit label reference, e.g., `1f`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct DigitLabelRef {
  /// The digit on the reference.
  pub digit: Digit,
  /// The direction the reference is in.
  pub dir: Direction,
}

/// A direction for a `DigitLabel` reference.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Direction {
  /// The forward direction, e.g., `1f`.
  Forward,
  /// The backward direction, e.g., `1b`.
  Backward,
}

/// A decimal digit, from 0 to 9.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Digit(u8);

impl Digit {
  /// Creates a new `Digit` with the given digit value.
  pub fn new(digit: u8) -> Option<Self> {
    match digit {
      0..=9 => Some(Digit(digit)),
      _ => None,
    }
  }

  /// Returns the inner digit value.
  pub fn into_inner(self) -> u8 {
    self.0
  }
}

/// An integer literal.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct IntLit {
  /// The value of this literal.
  pub value: Int,
  /// Whether this value was declared as a negative integer.
  pub is_neg: bool,
  /// Whether this value was declared as a "not" integer.
  pub is_not: bool,
  /// The "style" of this integer, i.e, the base it was parsed in.
  pub style: DigitStyle,
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

  /// Maps this `AddrExpr` by converting arguments contained within using a
  /// closure.
  ///
  /// The closure's first argument is the index of the argument, while the
  /// second argument is the argument itself.
  ///
  /// If the closure returns an error, the function returns that error
  /// immediately.
  pub fn map<U, E>(
    &self,
    mut f: impl FnMut(usize, &Arg) -> Result<U, E>,
  ) -> Result<AddrExpr<U>, E> {
    let addr = match self {
      Self::Acc => AddrExpr::Acc,
      Self::Imm(a) => AddrExpr::Imm(f(0, a)?),
      Self::Abs(a) => AddrExpr::Abs(f(0, a)?),
      Self::Idx(a, x) => AddrExpr::Idx(f(0, a)?, *x),
      Self::Ind(a) => AddrExpr::Ind(f(0, a)?),
      Self::IdxInd(a, x) => AddrExpr::IdxInd(f(0, a)?, *x),
      Self::IndIdx(a, x) => AddrExpr::IndIdx(f(0, a)?, *x),
      Self::IdxIndIdx(a, x, y) => AddrExpr::IdxIndIdx(f(0, a)?, *x, *y),
      Self::LongInd(a) => AddrExpr::LongInd(f(0, a)?),
      Self::LongIndIdx(a, x) => AddrExpr::LongIndIdx(f(0, a)?, *x),
      Self::Move(a, b) => AddrExpr::Move(f(0, a)?, f(1, b)?),
    };
    Ok(addr)
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
