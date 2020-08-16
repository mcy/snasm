//! Line-level syntactic constructs.
//!
//! An [`Atom`] represents the simplest single instruction that the assembler
//! can understand. There are fundamentally four kinds of atoms:
//! - [Instructions](../code/index.html), the most interesting kind of atom.
//! - Labels, which consist of a symbol (or a single digit) followed by a colon:
//!   `foo_bar:` or `5:`. These are used to give instructions concrete locations
//!   to jump to, and can be used to define linker symbols.
//! - [`Directive`]s, which are used to implement miscellaneous assembler
//!   commands. They are indicated by special symbols starting with a dot, and
//!   may be followed by a comma-separated list of [`Operand`] arguments.
//! - Empty atoms, which are used to anchor comments that don't apply to a
//!   "real" atom.
//!
//! Every atom may be followed by a [`Comment`]. A collection of atoms forms an
//! assembly [`Source`].
//!
//! [`Atom`]: struct.Atom.html
//! [`Directive`]: struct.Directive.html
//! [`Operand`]: ../operand/enum.Operand.html
//! [`Comment`]: ../src/enum.Comment.html
//! [`Source`]: ../src/enum.Source.html

use std::fmt;

use crate::syn::code::Code;
use crate::syn::fmt::ByteCounter;
use crate::syn::fmt::Format;
use crate::syn::fmt::Options;
use crate::syn::operand::Digit;
use crate::syn::operand::Operand;
use crate::syn::operand::Symbol;
use crate::syn::src::Comment;
use crate::syn::src::Span;

/// A syntactic atom.
///
/// An atom describes a "complete" assembler command, such as a label, a
/// directive such as `.origin`, or an actual instruction.
///
/// See the [module documentation](index.html) for syntax information.
#[derive(Clone, Debug)]
pub struct Atom<'asm> {
  /// The actual semantic content of the atom.
  pub inner: AtomType<'asm>,
  /// This atom's end-of-line comment, if it had one.
  pub comment: Option<Comment<'asm>>,
  /// Whether this atom was the last one on a line.
  pub has_newline: bool,
  /// The span this atom was parsed from, if any.
  pub span: Option<Span<'asm>>,
}

impl Format for Atom<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    self.inner.fmt(opts, w)?;

    if let Some(comment) = &self.comment {
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
      opts.force_newlines || self.has_newline || self.comment.is_some();
    if needs_newline {
      writeln!(w, "")?;
      w.reset_count();
    }

    Ok(())
  }
}
impl_display!(Atom<'_>);

/// The inner type of an [`Atom`].
///
/// [`Atom`]: struct.Atom.html
#[derive(Clone, Debug)]
pub enum AtomType<'asm> {
  /// A label definition: `foo:`.
  Label(Symbol<'asm>),

  /// A local digit label definition: `1:`.
  LocalLabel(Digit),

  /// A directive: `.origin $100`.
  Directive(Directive<'asm>),

  /// An instruction: `adc $ff, x`.
  ///
  /// Each instruction consists of a mnemonic, an optional width, and an
  /// optional address expression.
  Instruction(Code<'asm>),

  /// An empty atom, representing an empty line.
  Empty,
}

impl Format for AtomType<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    match self {
      AtomType::Label(sym) => {
        if w.count() > 0 {
          write!(w, " {}:", sym)?
        } else {
          write!(w, "{}:", sym)?
        }
      }
      AtomType::LocalLabel(d) => {
        if w.count() > 0 {
          write!(w, " {}:", d)?
        } else {
          write!(w, "{}:", d)?
        }
      }
      AtomType::Directive(dir) => dir.fmt(opts, w)?,
      AtomType::Instruction(ins) => ins.fmt(opts, w)?,
      AtomType::Empty => {}
    }
    Ok(())
  }
}
impl_display!(AtomType<'_>);

/// An assembler directive, which may be potentially unknown to the assembler.
#[derive(Clone, Debug)]
pub struct Directive<'asm> {
  /// The original symbol this directive was parsed with.
  pub sym: Symbol<'asm>,
  /// The arguments for this directive.
  pub args: Vec<Operand<'asm>>,
}

impl Format for Directive<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    if w.count() > 0 {
      write!(w, " {}", self.sym)?;
    } else {
      write!(w, "{}", self.sym)?;
    }
    for (i, arg) in self.args.iter().enumerate() {
      write!(w, " ")?;
      arg.fmt(opts, w)?;
      if i + 1 != self.args.len() {
        write!(w, ",")?;
      }
    }
    Ok(())
  }
}
impl_display!(Directive<'_>);
