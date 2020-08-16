//! Formatting facilities for SNASM AST.

use std::io;
use std::io::Write as _;

use crate::int::Width;
use crate::isa::Instruction;
use crate::syn::AddrExpr;
use crate::syn::AtomType;
use crate::syn::DigitStyle;
use crate::syn::Direction;
use crate::syn::DirectiveType;
use crate::syn::File;
use crate::syn::InstructionLine;
use crate::syn::IntLit;
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
pub fn print(opts: &Options, f: &File, w: impl io::Write) -> io::Result<()> {
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

        match &dir.ty {
          DirectiveType::Origin(int) => {
            write!(w, " ")?;
            pretty_print_operand(opts, &Operand::Int(*int), &mut w)?;
          }
          DirectiveType::Extern { sym, bank: None } => {
            write!(w, " {}", sym.name)?
          }
          DirectiveType::Extern {
            sym,
            bank: Some(bank),
          } => {
            write!(w, " {}, ", sym.name)?;
            pretty_print_operand(opts, &Operand::Int(*bank), &mut w)?;
          }
          DirectiveType::Global(sym) => write!(w, " {}", sym.name)?,
          DirectiveType::Data(bytes) => {
            for byte in bytes {
              write!(w, " ")?;
              pretty_print_operand(opts, &Operand::Int(*byte), &mut w)?;
              write!(w, ",")?;
            }
          }
          DirectiveType::Fill { value, count } => {
            write!(w, " ")?;
            pretty_print_operand(opts, &Operand::Int(*value), &mut w)?;
            write!(w, ", ")?;
            pretty_print_operand(opts, &Operand::Int(*count), &mut w)?;
          }
          DirectiveType::Zero(count) => {
            write!(w, " ")?;
            pretty_print_operand(opts, &Operand::Int(*count), &mut w)?;
          }
          DirectiveType::Unknown(args) => {
            for (i, arg) in args.iter().enumerate() {
              write!(w, " ")?;
              pretty_print_operand(opts, arg, &mut w)?;
              if i + 1 != args.len() {
                write!(w, ",")?;
              }
            }
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
            is_neg: false,
            is_not: false,
            style: DigitStyle::Hex,
          }))
        })
        .unwrap()
    }),
  };
  print_instruction_line(opts, &line, &mut ByteCounter::new(w))
}

fn pretty_print_operand(
  opts: &Options,
  op: &Operand,
  w: &mut impl io::Write,
) -> io::Result<()> {
  match op {
    Operand::Int(int) => {
      let mut value = int.value;
      if int.is_neg {
        value = -value;
        write!(w, "-")?;
      }
      if int.is_not {
        value = !value;
        write!(w, "!")?;
      }

      match (int.style, value) {
        (DigitStyle::Dec, n) => write!(w, "{}", n)?,
        (DigitStyle::Bin, n) => write!(w, "%{:b}", n)?,
        (DigitStyle::Hex, n) => write!(w, "${:x}", n)?,
      }

      let needs_ty = match int.value.width() {
        Width::I8 => false,
        Width::I16 => Width::I8.in_range(int.value.to_u32()),
        Width::I24 => {
          Width::I8.in_range(int.value.to_u32())
            || Width::I16.in_range(int.value.to_u32())
        }
      };
      if opts.always_include_suffix || needs_ty {
        write!(w, "_{}", int.value.width())?
      }
    }

    Operand::String(..) => unreachable!(),
    Operand::Symbol(s) => write!(w, "{}", s.name)?,
    Operand::DigitLabelRef(dlr) => match dlr.dir {
      Direction::Forward => write!(w, "{}f", dlr.digit.into_inner())?,
      Direction::Backward => write!(w, "{}b", dlr.digit.into_inner())?,
    },
  }

  Ok(())
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
