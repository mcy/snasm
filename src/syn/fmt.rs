//! Formatting facilities for SNASM AST.

use std::io;
use std::io::Write as _;

use crate::syn::AddrExpr;
use crate::syn::AtomType;
use crate::syn::DigitStyle;
use crate::syn::File;
use crate::syn::IntType;
use crate::syn::Operand;

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
#[derive(Clone, Debug)]
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
  /// Whether to always include a suffix for integer literals, or only when
  /// necessary.
  pub always_include_suffix: bool,
}

impl Default for Options {
  fn default() -> Self {
    Self {
      force_newlines: true,
      instruction_indent: 4,
      comment_justify_threshold: Some(26),
      always_include_suffix: false,
    }
  }
}

/// Prints out a `File` using the given options.
///
/// See [`Options`](struct.Options.html) for more details.
pub fn print(
  opts: &Options,
  f: &File,
  w: &mut impl io::Write,
) -> io::Result<()> {
  // Any time we write a "real" newline, we reset the counter, so that the
  // counter is just the the number of bytes since a newline.
  let mut w = ByteCounter::new(w);

  for atom in &f.atoms {
    match &atom.inner {
      AtomType::Label(sym) => {
        if w.count() > 0 {
          write!(w, " {}:", sym.name)?
        } else {
          write!(w, "{}:", sym.name)?
        }
      }
      AtomType::DigitLabel(val) => {
        if w.count() > 0 {
          write!(w, " {}:", val)?
        } else {
          write!(w, "{}:", val)?
        }
      }
      AtomType::Directive(name, args) => {
        if w.count() > 0 {
          write!(w, " {}", name.name)?;
        } else {
          write!(w, "{}", name.name)?;
        }
        for (i, arg) in args.iter().enumerate() {
          write!(w, " ")?;
          pretty_print_operand(opts, arg, &mut w)?;
          if i + 1 != args.len() {
            write!(w, ",")?;
          }
        }
      }
      AtomType::Instruction(mne, ty, expr) => {
        let on_margin = w.count() == 0;
        if on_margin {
          for _ in 0..opts.instruction_indent {
            write!(w, " ")?;
          }
        } else {
          write!(w, " ")?;
        }

        write!(w, "{}", mne.name())?;
        match ty {
          Some(IntType::I8) => write!(w, ".i8 ")?,
          Some(IntType::I16) => write!(w, ".i16")?,
          Some(IntType::I24) => write!(w, ".i24")?,
          _ => write!(w, "   ")?,
        }

        if expr.is_some() {
          if on_margin {
            write!(w, " ")?;
            // Round the count so far up to the indent width.
            while w.count() % opts.instruction_indent != 0 {
              write!(w, " ")?;
            }
          } else {
            write!(w, " ")?;
          }
        }

        match expr {
          Some(AddrExpr::Acc) => {
            write!(w, "a")?;
          }
          Some(AddrExpr::Imm(a)) => {
            write!(w, "#")?;
            pretty_print_operand(opts, a, &mut w)?;
          }
          Some(AddrExpr::Abs(a)) => {
            pretty_print_operand(opts, a, &mut w)?;
          }
          Some(AddrExpr::Idx(a, x)) => {
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, ", {}", x.name())?;
          }
          Some(AddrExpr::Ind(a)) => {
            write!(w, "(")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, ")")?;
          }
          Some(AddrExpr::IdxInd(a, x)) => {
            write!(w, "(")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, ", {})", x.name())?;
          }
          Some(AddrExpr::IndIdx(a, x)) => {
            write!(w, "(")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, "), {}", x.name())?;
          }
          Some(AddrExpr::IdxIndIdx(a, x, y)) => {
            write!(w, "(")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, ", {}), {}", x.name(), y.name())?;
          }
          Some(AddrExpr::LongInd(a)) => {
            write!(w, "[")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, "]")?;
          }
          Some(AddrExpr::LongIndIdx(a, x)) => {
            write!(w, "[")?;
            pretty_print_operand(opts, a, &mut w)?;
            write!(w, "], {}", x.name())?;
          }
          None => {}
        }
      }
      AtomType::Empty => {}
    }

    if let Some(comment) = &atom.comment {
      let spaces_needed = if w.count() == 0 {
        0
      } else if let Some(len) = opts.comment_justify_threshold {
        if len >= w.count() + 2 {
          len - w.count()
        } else {
          2
        }
      } else {
        2
      };

      for _ in 0..spaces_needed {
        write!(w, " ")?;
      }
      write!(w, "{}", comment.text)?;
    }

    let needs_newline =
      opts.force_newlines || atom.has_newline || atom.comment.is_some();
    if needs_newline {
      writeln!(w, "")?;
      w.reset_count();
    }
  }

  Ok(())
}

fn pretty_print_operand(
  opts: &Options,
  op: &Operand,
  w: &mut impl io::Write,
) -> io::Result<()> {
  match op {
    Operand::Int(int) => {
      let value = int.value;
      match int.style {
        DigitStyle::Dec => match int.ty {
          IntType::I8 if int.is_negative() => write!(w, "{}", value as i8)?,
          IntType::I16 if int.is_negative() => write!(w, "{}", value as i16)?,
          IntType::I24 if int.is_negative() => write!(w, "{}", value as i32)?,
          IntType::I8 => write!(w, "{}", value as u8)?,
          IntType::I16 => write!(w, "{}", value as u16)?,
          IntType::I24 => write!(w, "{}", value & 0xffffff)?,
        },
        DigitStyle::Hex => match int.ty {
          IntType::I8 => write!(w, "${:x}", value as u8)?,
          IntType::I16 => write!(w, "${:x}", value as u16)?,
          IntType::I24 => write!(w, "${:x}", value & 0xffffff)?,
        },
        DigitStyle::Bin => match int.ty {
          IntType::I8 => write!(w, "%{:b}", value as u8)?,
          IntType::I16 => write!(w, "%{:b}", value as u16)?,
          IntType::I24 => write!(w, "%{:b}", value & 0xffffff)?,
        },
      }

      let needs_ty = match int.ty {
        IntType::I8 => false,
        IntType::I16 => value < 0x100 && value > -0x80,
        IntType::I24 => value < 0x10000 && value > -0x8000,
      };
      if opts.always_include_suffix || needs_ty {
        match int.ty {
          IntType::I8 => write!(w, "i8")?,
          IntType::I16 => write!(w, "i16")?,
          IntType::I24 => write!(w, "i24")?,
        }
      }
    }

    Operand::String(..) => unreachable!(),
    Operand::Symbol(s) => write!(w, "{}", s.name)?,
    Operand::LabelRef { value, is_forward } => {
      if *is_forward {
        write!(w, "{}f", value)?
      } else {
        write!(w, "{}b", value)?
      }
    }
  }

  Ok(())
}

/// Helper for wrapping a `Write`, which keeps track of the total number of
/// bytes written.
struct ByteCounter<'a, W> {
  w: &'a mut W,
  count: usize,
}

impl<'a, W: io::Write> ByteCounter<'a, W> {
  fn new(w: &'a mut W) -> Self {
    Self { w, count: 0 }
  }

  /// Resets the counter.
  fn reset_count(&mut self) {
    self.count = 0;
  }

  /// Gets the number of bytes written so far.
  fn count(&self) -> usize {
    self.count
  }
}

impl<'a, W: io::Write> io::Write for ByteCounter<'a, W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    let len = self.w.write(buf)?;
    self.count += len;
    Ok(len)
  }

  fn flush(&mut self) -> io::Result<()> {
    self.w.flush()
  }
}
