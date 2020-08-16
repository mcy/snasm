//! Formatting facilities for SNASM AST.

use std::fmt;
use std::io;

use crate::isa::Instruction;
use crate::syn::code::Code;
use crate::syn::int::DigitStyle;
use crate::syn::int::IntLit;
use crate::syn::int::PrefixStyle;
use crate::syn::operand::Operand;

/// Formatter options.
///
/// This type implements `Default` to provide "sane defaults" for the formatter,
/// which is intended to be used with record update syntax:
/// ```
/// # use snasm::syn::fmt::Options;
/// let opts = Options {
///   instruction_indent: 2,
///   ..Options::default(),
/// };
/// ```
#[derive(Copy, Clone, Debug)]
pub struct Options {
  /// Force newlines after every atom.
  ///
  /// This is on by default; in effect, it performs the following conversion:
  /// ```text
  /// my_function: xyz ($1234, x)
  /// ; Becomes...
  /// my_function:
  ///     xyz ($1234, x)
  /// ```
  pub force_newlines: bool,
  /// The number of spaces to indent an instruction on a new line.
  ///
  /// Defaults to 4 spaces.
  pub instruction_indent: usize,
  /// The number of bytes to justify an end-of-line comment to. This option
  /// is measured in bytes, rather than characters.
  ///
  /// Defaults to 16 bytes.
  pub comment_justify_threshold: Option<usize>,
}

impl Default for Options {
  fn default() -> Self {
    Self {
      force_newlines: true,
      instruction_indent: 4,
      comment_justify_threshold: Some(26),
    }
  }
}

/// A formattable type.
///
/// This trait is *somewhat* like `Display`, that allows threading through an
/// `Options`.
pub trait Format {
  /// Formats `self`, using `options`.
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result;
}

/// A helper type for taking a type which implements `Format` and making it
/// usable with format strings.
pub struct Display<'a, T> {
  value: &'a T,
  options: Options,
}

impl<'a, T> Display<'a, T> {
  /// Creates a new `Display` for `value`, with default options.
  pub fn new(value: &'a T) -> Self {
    Self {
      value,
      options: Options::default(),
    }
  }

  /// Replaces the current `Options` with the given `options`.
  pub fn with(mut self, options: Options) -> Self {
    self.options = options;
    self
  }
}

impl<T: Format> fmt::Display for Display<'_, T> {
  #[inline]
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    Format::fmt(self.value, self.options, &mut ByteCounter::new(f))
  }
}

macro_rules! impl_display {
  ($ty:ty) => {
    impl std::fmt::Display for $ty {
      #[inline]
      fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(&$crate::syn::fmt::Display::new(self), f)
      }
    }
  };
}

/// Prints out an `Instruction` using the given options.
///
/// See [`Options`](struct.Options.html) for more details.
pub fn print_instruction(
  opts: Options,
  inst: Instruction,
  mut w: impl io::Write,
) -> io::Result<()> {
  let line = Code {
    mnemonic: inst.mnemonic(),
    width: None,
    addr: inst.addressing_mode().map(|addr| {
      addr
        .map(|_, &int| -> Result<_, ()> {
          Ok(Operand::Int(IntLit {
            value: int,
            unary: None,
            style: DigitStyle::Hex(PrefixStyle::Classic),
          }))
        })
        .unwrap()
    }),
  };
  write!(w, "{}", Display::new(&line).with(opts))
}

/// Helper for wrapping a `fmt::Write`, which keeps track of the total number of
/// bytes written.
pub struct ByteCounter<W> {
  w: W,
  count: usize,
}

impl<W> ByteCounter<W> {
  /// Creates a new `ByteCounter`.
  pub fn new(w: W) -> Self {
    Self { w, count: 0 }
  }

  /// Resets the counter.
  pub fn reset_count(&mut self) {
    self.count = 0;
  }

  /// Gets the number of bytes written so far.
  pub fn count(&self) -> usize {
    self.count
  }
}

impl<W: fmt::Write> ByteCounter<W> {
  #[doc(hidden)]
  pub fn write_fmt(&mut self, args: fmt::Arguments) -> fmt::Result {
    fmt::Write::write_fmt(self, args)
  }
}

impl<W: fmt::Write> fmt::Write for ByteCounter<W> {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    self.count += s.len();
    self.w.write_str(s)
  }
}
