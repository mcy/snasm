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

use crate::syn::code::Code;
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

/// The inner type of an [`Atom`].
///
/// [`Atom`]: struct.Atom.html
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
  Instruction(Code<'asm>),

  /// An empty atom, representing an empty line.
  Empty,
}

/// An assembler directive, which may be potentially unknown to the assembler.
#[derive(Clone, Debug)]
pub struct Directive<'asm> {
  /// The original symbol this directive was parsed with.
  pub sym: Symbol<'asm>,
  /// The arguments for this directive.
  pub args: Vec<Operand<'asm>>,
}
