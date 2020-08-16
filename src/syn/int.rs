//! Integer-literal syntax components.
//!
//! A SNASM integer can be formatted as decimal, binary, or hexadecimal, with
//! the following syntaxes:
//! - Decimal: `0`, `123`, etc.
//! - Binary: `%10` (65816-style), `0b1111` (C-style).
//! - Hexadecimal: `$dead` (65816-style), `0x1ee7` (C-style); case-insensitive.
//!
//! Additionally, underscores may be interespersed throughout a literal, except
//! as the first character, to separate groups of digits: `1_000`, `$ff_ff`,
//! `0b1___1`.
//!
//! Each integer literal has an associated type: `i8`, `i16`, or `i24`. By
//! default, the type is infered as the smallest that fits the integer, so `255`
//! is `i8`, but `256` is `i16`. This type can be forced with a prefix: `255i16`
//! always has type `i16`. An underscore can be included as a separator, for
//! readablity: `0_i24` (this is the formatter's default).
//!
//! Additionally, a literal may be prefixed with `-` or `!`, which will convert
//! its value to its two's or one's completement, within the width of its type.
//! This, `-1` is equivalent to `$ff`, not `$ffffff`. Integers are not
//! meaningfully signed or unsigned; when using two's complement, care should be
//! taken to pick the right width for a literal.

use std::fmt;

use crate::int::Int;
use crate::int::Width;
use crate::syn::fmt::ByteCounter;
use crate::syn::fmt::Format;
use crate::syn::fmt::Options;

/// An integer literal.
///
/// An `IntLit` consists of an [`Int`] value, along with metadata about how the
/// integer was formatted when it was parsed. The original apparence (modulo
/// an unnecessary type suffix) can be recovered via this type's [`Display`]
/// implementation.
///
/// Currently, `IntLit`s do not remember the casing of hexadecimal digits, or
/// any underscores present. This will be fixed eventually.
///
/// See the [module documentation](index.html) for syntax information.
///
/// [`Int`]: ../../int/struct.Int.html
/// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct IntLit {
  /// The value of this literal. This is the value *after* applying any
  /// operations present on the literal.
  pub value: Int,
  /// An unary operation applied to this literal, if one was present.
  pub unary: Option<Unary>,
  /// The "style" of this digits, i.e, the base it was parsed in and the
  /// prefix it had, if any.
  pub style: DigitStyle,
}

impl Format for IntLit {
  fn fmt<W: fmt::Write>(
    &self,
    _: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    let value = match self.unary {
      Some(Unary::Neg) => {
        write!(w, "-")?;
        -self.value
      }
      Some(Unary::Not) => {
        write!(w, "!")?;
        !self.value
      }
      None => self.value,
    };

    match (self.style, value) {
      (DigitStyle::Dec, n) => write!(w, "{}", n)?,
      (DigitStyle::Bin(PrefixStyle::Classic), n) => write!(w, "%{:b}", n)?,
      (DigitStyle::Bin(PrefixStyle::Modern), n) => write!(w, "0b{:b}", n)?,
      (DigitStyle::Hex(PrefixStyle::Classic), n) => write!(w, "${:x}", n)?,
      (DigitStyle::Hex(PrefixStyle::Modern), n) => write!(w, "0x{:x}", n)?,
    }

    let needs_ty =
      Some(self.value.width()) != Width::smallest_for(self.value.to_u32());
    if needs_ty {
      write!(w, "_{}", self.value.width())?
    }

    Ok(())
  }
}
impl_display!(IntLit);

/// An unary operation applied to an integer literal.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Unary {
  /// Negation, aka two's complement.
  Neg,
  /// Not, aka one's completement.
  Not,
}

/// A digit style: decimal, hex, or binary.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum DigitStyle {
  /// Decimal style: `123`.
  Dec,
  /// Hex style: `$dead`.
  Hex(PrefixStyle),
  /// Binary style: `%0110`.
  Bin(PrefixStyle),
}

impl DigitStyle {
  /// Returns this style's associated radix.
  pub fn radix(self) -> u32 {
    match self {
      Self::Dec => 10,
      Self::Hex(_) => 16,
      Self::Bin(_) => 2,
    }
  }
}

/// A prefix style, i.e., `$ff` vs. `0xff`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum PrefixStyle {
  /// Classic style: `$ff` and `%10`.
  Classic,
  /// Modern, C-style: `0xff` and `0b10`.
  Modern,
}
