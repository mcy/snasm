//! Instruction-related syntax components.
//!
//! Instructions. represented by the [`Code`] type, are literal 65816
//! instructions. which consist of at most three parts:
//! - A three-character, case insesnsitive mnemonic, like `adc` or `tax`.
//! - An optional width parameter following immediately thereafter, like `.i18`.
//! - An optional operand, in one of various addressing modes.
//!
//! Some examples:
//! ```text
//! adc     $1235, x
//! lda.i24 #$100u16
//! brk
//! asl     a
//! jmp     [$f0_f0_f0]
//! ```
//!
//! # Addressing Modes
//! 65816 has a myriad of very CISC-ey addressing modes. SNASM simplifies these
//! into the following, generic syntactic forms:
//!
//! | Name                       | Syntax                      |
//! |----------------------------|-----------------------------|
//! | Accumulator                | `a`                         |
//! | Immediate                  | `#<operand>`                |
//! | Absolute                   | `<operand>`                 |
//! | Indirect                   | `(<operand>)`               |
//! | Indexed absolute           | `<operand>, <reg>`          |
//! | Pre-indexed indirect       | `(<operand>, <reg>)`        |
//! | Post-indexed indirect      | `(<operand>), <reg>`        |
//! | Bi-indexed indirect        | `(<operand>, <reg>), <reg>` |
//! | Long indirect              | `[<operand>]`               |
//! | Long post-indexed indirect | `[<operand>], <reg>`        |
//!
//! `<operand>` is any operand expression, while `<reg>` is any of the `x`, `y`,
//! or `s` registers. Of course, not all combinations of addressing modes,
//! operand types, and registers are valid instructions; that information can be
//! found in the [`isa` module](../../isa/index.html).
//!
//! An addressing mode is described by the [`AddrExpr`] type.
//!
//! [`Code`]: struct.Code.html
//! [`AddrExpr`]: enum.AddrExpr.html

use std::fmt;

use crate::int::Width;
use crate::isa::Mnemonic;
use crate::syn::fmt::ByteCounter;
use crate::syn::fmt::Display;
use crate::syn::fmt::Format;
use crate::syn::fmt::Options;
use crate::syn::operand::Operand;

/// An unassembled instruction.
///
/// This type tracks an individual instruction that may have unresolved symbols,
/// or may not even correspond to a valid instruction at all!
///
/// See the [module documentation](index.html) for information on the syntax.
#[derive(Clone, Debug)]
pub struct Code<'asm> {
  /// The instruction's mnemonic.
  pub mnemonic: Mnemonic,
  /// A width suffix, like `.i8`.
  pub width: Option<Width>,
  /// The addressing mode and operand for the instruction.
  pub addr: Option<AddrExpr<Operand<'asm>>>,
}

impl Format for Code<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    let on_margin = w.count() == 0;
    if on_margin {
      for _ in 0..opts.instruction_indent {
        write!(w, " ")?;
      }
    } else {
      write!(w, " ")?;
    }
    write!(w, "{}", self.mnemonic.name())?;
    match self.width {
      Some(width) => write!(w, ".{:<3}", width)?,
      None if self.addr.is_some() => write!(w, "    ")?,
      _ => {}
    }

    if let Some(addr) = &self.addr {
      if on_margin && opts.instruction_indent != 0 {
        write!(w, " ")?;
        // Round the count so far up to the indent width.
        while w.count() % opts.instruction_indent != 0 {
          write!(w, " ")?;
        }
      } else {
        write!(w, " ")?;
      }

      addr.fmt(opts, w)?;
    }
    Ok(())
  }
}
impl_display!(Code<'_>);

/// A "address expression", encompassing all of the syntactic variations
/// of addressing modes.
///
/// This type is generic in the type of the "argument", which is usually an
/// unresolved operand. However, since it is tedious to write code to handle so
/// many syntactic forms, we've made this type re-useable.
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

impl<Arg: Format> Format for AddrExpr<Arg> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    match self {
      Self::Acc => write!(w, "a"),
      Self::Imm(a) => {
        write!(w, "#")?;
        a.fmt(opts, w)
      }
      Self::Abs(a) => a.fmt(opts, w),
      Self::Idx(a, x) => {
        a.fmt(opts, w)?;
        write!(w, ", {}", x)
      }
      Self::Ind(a) => {
        write!(w, "(")?;
        a.fmt(opts, w)?;
        write!(w, ")")
      }
      Self::IdxInd(a, x) => {
        write!(w, "(")?;
        a.fmt(opts, w)?;
        write!(w, ", {})", x)
      }
      Self::IndIdx(a, x) => {
        write!(w, "(")?;
        a.fmt(opts, w)?;
        write!(w, "), {}", x)
      }
      Self::IdxIndIdx(a, x, y) => {
        write!(w, "(")?;
        a.fmt(opts, w)?;
        write!(w, ", {}), {}", x, y)
      }
      Self::LongInd(a) => {
        write!(w, "[")?;
        a.fmt(opts, w)?;
        write!(w, "]")
      }
      Self::LongIndIdx(a, x) => {
        write!(w, "[")?;
        a.fmt(opts, w)?;
        write!(w, "], {}", x)
      }
      Self::Move(a, b) => {
        a.fmt(opts, w)?;
        write!(w, ", ")?;
        b.fmt(opts, w)
      }
    }
  }
}

impl<Arg: Format> fmt::Display for AddrExpr<Arg> {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(&Display::new(self), f)
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

impl fmt::Display for IdxReg {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    fmt::Display::fmt(&self.name(), f)
  }
}
