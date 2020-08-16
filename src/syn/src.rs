//! Top-level syntax components, representing source files.

use std::fmt;

use crate::syn::atom::Atom;
use crate::syn::fmt::ByteCounter;
use crate::syn::fmt::Format;
use crate::syn::fmt::Options;
use crate::syn::parse;
use crate::syn::parse::PestSpan;

pub use parse::Error;

/// A line comment in a file.
///
/// Comments consist of a `;` character followed by text, until the end of the
/// line.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Comment<'asm> {
  /// The text of the comment, including the comment character.
  ///
  /// E.g., `"; This is a function."`.
  pub text: &'asm str,
}

/// An assembly source.
///
/// An assembly source consists of a sequence of *atoms*, representing different
/// instructions for the assembler. By and large, these are mostly code
/// instructions, labels, and miscellaneous assembler directives.
///
/// A reference to a `Source` can be used as an iterator over its atoms.
#[derive(Clone, Debug)]
pub struct Source<'asm> {
  /// The name of this file.
  pub(in crate::syn) name: Option<&'asm str>,
  /// The atoms that make up this file.
  pub(in crate::syn) atoms: Vec<Atom<'asm>>,
}

impl Format for Source<'_> {
  fn fmt<W: fmt::Write>(
    &self,
    opts: Options,
    w: &mut ByteCounter<W>,
  ) -> fmt::Result {
    for atom in self {
      atom.fmt(opts, w)?;
    }
    Ok(())
  }
}
impl_display!(Source<'_>);

impl<'asm> Source<'asm> {
  /// Parses a source file out of `text`, giving it the given `name`.
  pub fn parse(
    name: Option<&'asm str>,
    text: &'asm str,
  ) -> Result<Self, Error<'asm>> {
    parse::parse(name, text)
  }

  /// Returns the name of this source file.
  pub fn file_name(&self) -> Option<&'asm str> {
    self.name
  }

  /// Returns an iterator over the atoms in this fource file.
  pub fn iter(&self) -> impl Iterator<Item = &Atom<'asm>> {
    self.atoms.iter()
  }
}

impl<'atom, 'asm> IntoIterator for &'atom Source<'asm> {
  type Item = &'atom Atom<'asm>;
  type IntoIter = std::slice::Iter<'atom, Atom<'asm>>;

  fn into_iter(self) -> Self::IntoIter {
    self.atoms.iter()
  }
}

/// A source span, indicating a region within a [`Source`]'s original text.
///
/// [`Source`] struct.Source.html
#[derive(Clone)]
pub struct Span<'asm> {
  /// The name of the file.
  pub(in crate::syn) name: Option<&'asm str>,
  /// A span within the file.
  pub(in crate::syn) span: PestSpan<'asm>,
}

impl<'asm> Span<'asm> {
  /// Returns the name of the file this `Span` refers to.
  pub fn file_name(&self) -> Option<&'asm str> {
    self.name
  }

  fn name_or(&self) -> &'asm str {
    match self.name {
      Some(name) => name,
      None => "<?>",
    }
  }

  /// Returns the offset at which this `Span` starts.
  pub fn start_byte(&self) -> usize {
    self.span.start()
  }

  /// Returns the offset at which this `Span` ends.
  pub fn end_byte(&self) -> usize {
    self.span.end()
  }

  /// Returns the line and column this `Span` starts at, both zero-indexed.
  pub fn start_position(&self) -> (usize, usize) {
    self.span.start_pos().line_col()
  }

  /// Returns the line and column this `Span` ends at, both zero-indexed.
  pub fn end_position(&self) -> (usize, usize) {
    self.span.end_pos().line_col()
  }

  /// Returns the text that this span refers to.
  pub fn text(&self) -> &'asm str {
    self.span.as_str()
  }

  /// Returns the text of the first line that this `Span` intersects.
  pub fn first_line(&self) -> &'asm str {
    self.span.start_pos().line_of()
  }
}

impl fmt::Debug for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(
      f,
      "{:?}[{}..{}]",
      self.name_or(),
      self.start_byte(),
      self.end_byte()
    )
  }
}

impl fmt::Display for Span<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let (line, col) = self.start_position();
    write!(f, "{:?}:{}:{}", self.name_or(), line + 1, col + 1)
  }
}