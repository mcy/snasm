//! Error printing facilities.
//!
//! These functions are used to simplify the display of various SNASM errors to
//! the user. The [`Error`] trait describes how a Rust error type can be
//! converted into a simple diagonstic.
//!
//! [`Error`]: trait.Error.html

use std::fmt;
use std::io;
use std::path::Path;

use crate::syn::src::Span;

/// An error which can be described as a diagnostic.
///
/// Types that implement `Error` must also implement [`std::fmt::Display`]. For
/// the user-displayed error to look right, this implementation should only be
/// one line long.
///
/// [`std::fmt::Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
pub trait Error: fmt::Debug + fmt::Display {
  /// Returns a `Cause` describing the input that resulted in the error.
  fn cause(&self) -> Cause<'_>;
  /// Returns an action this error is associated with, if any at all.
  fn action(&self) -> Option<Action>;
}

/// A collection of errors that may built up over the course of an action.
///
/// The type parameter `E` should be a type implementing [`Error`].
///
/// [`Error`]: trait.Error.html
pub struct Errors<E>(Vec<E>);

impl<E> Errors<E> {
  /// Creates an empty `Errors`.
  pub fn new() -> Self {
    Errors(Vec::new())
  }

  /// Returns true if this `Errors` hasn't had any errors added yet.
  pub fn is_ok(&self) -> bool {
    self.0.is_empty()
  }

  /// Adds a new error to this `Errors`.
  pub fn push(&mut self, error: E) {
    self.0.push(error);
  }

  /// Extends this `Errors` by consuming another `Errors`.
  pub fn extend(&mut self, mut errors: Errors<E>) {
    self.0.reserve(errors.0.len());
    for e in errors.0.drain(..) {
      self.push(e);
    }
  }
}

impl<E: Error> Errors<E> {
  /// Dumps this collection of errors as user-displayable text into `sink`.
  ///
  /// Returns `Ok(true)` if anything was written.
  pub fn dump_to(&self, mut sink: impl io::Write) -> io::Result<bool> {
    if self.0.is_empty() {
      return Ok(false);
    }

    for (i, error) in self.0.iter().enumerate() {
      writeln!(sink, "error: {}", error)?;
      match error.cause() {
        Cause::Span(span) => {
          if let Some(action) = error.action() {
            writeln!(sink, "  while {} {}", action.describe(), span)?;
          } else {
            writeln!(sink, "  at {}", span)?;
          }
          let (line, _) = span.start_position();
          writeln!(
            sink,
            "{} | {}",
            line + 1,
            span.first_line().trim_matches('\n')
          )?;
        }
        Cause::File(path) => {
          if let Some(action) = error.action() {
            writeln!(sink, "  while {} {}", action.describe(), path.display())?;
          } else {
            writeln!(sink, "  at {}", path.display())?;
          }
        }
      }

      if i != self.0.len() - 1 {
        writeln!(sink, "")?;
      }
    }

    Ok(true)
  }

  /// Calls `dump_to()` on `stderr`, exiting the process with the given
  /// `exit_code` if any errors are present.
  pub fn dump_and_die(self, code: i32) {
    // Writing to stderr is fairly unlikely to fail, so panicking is a fine
    // response here.
    if self.dump_to(io::stderr()).unwrap() {
      eprintln!("");
      eprintln!("error: there were {} errors", self.0.len());
      std::process::exit(code)
    }
  }
}

/// The place where an error occured, to varrying degrees of specificity.
pub enum Cause<'a> {
  /// A span within a file, allowing the offending line to be shown to the user.
  Span(Span<'a>),
  /// A file, for when we don't know much about where the error came from
  /// within.
  File(&'a Path),
}

/// An action that SNASM performs, which an error may be associated with.
pub enum Action {
  /// The parsing step, converting text into source.
  Parsing,
  /// The assembly step, converting sources into objects.
  Assembling,
  /// The linking step, converting objects into a ROM.
  Linking,
}

impl Action {
  fn describe(self) -> &'static str {
    match self {
      Self::Parsing => "parsing",
      Self::Assembling => "assembling",
      Self::Linking => "linking",
    }
  }
}
