//! Operand-related syntax components.

use std::fmt;

use crate::syn::fmt::ByteCounter;
use crate::syn::fmt::Format;
use crate::syn::fmt::Options;
use crate::syn::int::IntLit;

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
  /// A local label reference, like `1f` or `2b`.
  Local(LocalLabel),
}

impl Format for Operand<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    match self {
      Operand::Int(i) => i.fmt(opts, w),
      Operand::Symbol(s) => write!(w, "{}", s),
      Operand::Local(l) => write!(w, "{}", l),
      Operand::String(..) => unreachable!(),
    }
  }
}
impl_display!(Operand<'_>);

/// A symbol, a generic identifier.
///
/// `Symbols` usually indicate the location within a program, but may be given
/// special meaning by directives.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol<'asm> {
  /// The name of this symbol.
  pub name: &'asm str,
}

impl fmt::Display for Symbol<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(self.name, f)
  }
}

/// A local label reference, e.g., `1f`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum LocalLabel {
  /// A forward reference, e.g., `1f`.
  Forward(Digit),
  /// A backward reference, e.g., `2f`.
  Backward(Digit),
}

impl LocalLabel {
  /// Returns the digit associated with this reference.
  pub fn digit(self) -> Digit {
    match self {
      Self::Forward(d) => d,
      Self::Backward(d) => d,
    }
  }
}

impl fmt::Display for LocalLabel {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Forward(d) => write!(f, "{}f", d),
      Self::Backward(d) => write!(f, "{}b", d),
    }
  }
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

impl fmt::Display for Digit {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(&self.0, f)
  }
}
