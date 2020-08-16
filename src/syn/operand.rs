//! Operand-related syntax components.

use crate::syn::int::IntLit;

/// A symbol, a generic identifier.
///
/// `Symbols` usually indicate the location within a program, but may be given
/// special meaning by directives.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol<'asm> {
  /// The name of this symbol.
  pub name: &'asm str,
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
