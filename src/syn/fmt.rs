//! Formatting facilities for SNASM AST.

use std::io;
use std::io::Write as _;

use crate::isa::Instruction;
use crate::syn::AddrExpr;
use crate::syn::AtomType;
use crate::syn::Direction;
use crate::syn::src::Source;
use crate::syn::InstructionLine;
use crate::syn::Operand;
use crate::syn::int::DigitStyle;
use crate::syn::int::PrefixStyle;
use crate::syn::int::IntLit;

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

/// Prints out a `Source` using the given options.
///
/// See [`Options`](struct.Options.html) for more details.
pub fn print(opts: &Options, f: &Source, w: impl io::Write) -> io::Result<()> {
  // Any time we write a "real" newline, we reset the counter, so that the
  // counter is just the the number of bytes since a newline.
  let mut w = ByteCounter::new(w);

  for atom in f {
    match &atom.inner {
      AtomType::Label(sym) => {
        if w.count() > 0 {
          write!(w, " {}:", sym.name)?
        } else {
          write!(w, "{}:", sym.name)?
        }
      }
      AtomType::DigitLabel(d) => {
        if w.count() > 0 {
          write!(w, " {}:", d.into_inner())?
        } else {
          write!(w, "{}:", d.into_inner())?
        }
      }
      AtomType::Directive(dir) => {
        if w.count() > 0 {
          write!(w, " {}", dir.sym.name)?;
        } else {
          write!(w, "{}", dir.sym.name)?;
        }
        for (i, arg) in dir.args.iter().enumerate() {
          write!(w, " ")?;
          pretty_print_operand(opts, arg, &mut w)?;
          if i + 1 != dir.args.len() {
            write!(w, ",")?;
          }
        }
      }
      AtomType::Instruction(ins) => {
        print_instruction_line(opts, ins, &mut w)?;
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

fn print_instruction_line(
  opts: &Options,
  inst: &InstructionLine,
  mut w: &mut ByteCounter<impl io::Write>,
) -> io::Result<()> {
  let on_margin = w.count() == 0;
  if on_margin {
    for _ in 0..opts.instruction_indent {
      write!(w, " ")?;
    }
  } else {
    write!(w, " ")?;
  }
  write!(w, "{}", inst.mne.name())?;
  match inst.width {
    Some(width) => write!(w, ".{:<3}", width)?,
    None => write!(w, "    ")?,
  }

  if inst.addr.is_some() {
    if on_margin && opts.instruction_indent != 0 {
      write!(w, " ")?;
      // Round the count so far up to the indent width.
      while w.count() % opts.instruction_indent != 0 {
        write!(w, " ")?;
      }
    } else {
      write!(w, " ")?;
    }
  }

  match &inst.addr {
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
    Some(AddrExpr::Move(a, b)) => {
      pretty_print_operand(opts, a, &mut w)?;
      write!(w, ", ")?;
      pretty_print_operand(opts, b, &mut w)?;
    }
    None => {}
  }
  Ok(())
}

/// Prints out an `Instruction` using the given options.
///
/// See [`Options`](struct.Options.html) for more details.
pub fn print_instruction(
  opts: &Options,
  inst: Instruction,
  w: impl io::Write,
) -> io::Result<()> {
  let line = InstructionLine {
    mne: inst.mnemonic(),
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
  print_instruction_line(opts, &line, &mut ByteCounter::new(w))
}

fn pretty_print_operand(
  _: &Options,
  op: &Operand,
  w: &mut impl io::Write,
) -> io::Result<()> {
  match op {
    Operand::Int(int) => write!(w, "{}", int),
    Operand::Symbol(s) => write!(w, "{}", s.name),
    Operand::DigitLabelRef(dlr) => match dlr.dir {
      Direction::Forward => write!(w, "{}f", dlr.digit.into_inner()),
      Direction::Backward => write!(w, "{}b", dlr.digit.into_inner()),
    },
    Operand::String(..) => unreachable!(),
  }
}

/// Helper for wrapping a `Write`, which keeps track of the total number of
/// bytes written.
struct ByteCounter<W> {
  w: W,
  count: usize,
}

impl<'a, W: io::Write> ByteCounter<W> {
  fn new(w: W) -> Self {
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

impl<W: io::Write> io::Write for ByteCounter<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    let len = self.w.write(buf)?;
    self.count += len;
    Ok(len)
  }

  fn flush(&mut self) -> io::Result<()> {
    self.w.flush()
  }
}
