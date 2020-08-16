//! Functions for manipulating different kinds of symbol tables.

use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::syn::atom::Atom;
use crate::syn::operand::Digit;
use crate::syn::operand::DigitLabelRef;
use crate::syn::operand::Direction;
use crate::syn::operand::Symbol;

/// A symbol table.
///
/// A symbol table is a map of symbols to some type `T`, tracking which atom
/// caused the symbol to be defined.
///
/// A symbol table also includes an in-built `DigitLabelTable`, for performing
/// digit label lookups.
#[derive(Clone, Debug)]
pub struct SymbolTable<'atom, 'asm, T> {
  table: HashMap<SynthSymbol<'asm>, (&'atom Atom<'asm>, T)>,

  digit_table: DigitLabelTable<u64>,
  digit_counter: u64,
}

/// Helper enum for implmenting digit lookups within a symbol table.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum SynthSymbol<'asm> {
  Real(Symbol<'asm>),
  Synth(u64),
}

impl<'atom, 'asm, T> SymbolTable<'atom, 'asm, T> {
  /// Creates a new `SymbolTable`.
  pub fn new() -> Self {
    Self {
      table: HashMap::new(),
      digit_table: DigitLabelTable::new(),
      digit_counter: 0,
    }
  }

  /// Attempts to define `sym` with the value `x`.
  ///
  /// If this is a re-definition, the definition fails, and the `Atom` that
  /// originally defined the entry is returned, instead.
  pub fn define(
    &mut self,
    sym: Symbol<'asm>,
    atom: &'atom Atom<'asm>,
    x: T,
  ) -> Result<(), &'atom Atom<'asm>> {
    match self.table.entry(SynthSymbol::Real(sym)) {
      Entry::Vacant(e) => {
        e.insert((atom, x));
        Ok(())
      }
      Entry::Occupied(e) => Err(&e.get().0),
    }
  }

  /// Looks up the symbol `sym` in this `SymbolTable`.
  pub fn lookup(
    &mut self,
    sym: Symbol<'asm>,
  ) -> Option<&mut (&'atom Atom<'asm>, T)> {
    self.table.get_mut(&SynthSymbol::Real(sym))
  }

  /// Defines a digit symbol with the given digit and index, with the value `x`.
  pub fn define_digit(
    &mut self,
    digit: Digit,
    atom_idx: usize,
    atom: &'atom Atom<'asm>,
    x: T,
  ) {
    let id = self.digit_counter;
    self.digit_counter += 1;
    self.digit_table.define(digit, atom_idx, id);
    self.table.insert(SynthSymbol::Synth(id), (atom, x));
  }

  /// Looks up the digit `digit` defined at the given `atom_idx`.
  pub fn lookup_digit_at_def(
    &mut self,
    digit: Digit,
    atom_idx: usize,
  ) -> Option<&mut (&'atom Atom<'asm>, T)> {
    let id = self.digit_table.find_definition(digit, atom_idx).copied();
    id.and_then(move |id| self.table.get_mut(&SynthSymbol::Synth(id)))
  }

  /// Looks up the reference `label_ref` with respect to the given atom index.
  pub fn lookup_digit(
    &mut self,
    label_ref: DigitLabelRef,
    current_idx: usize,
  ) -> Option<&mut (&'atom Atom<'asm>, T)> {
    let id = self
      .digit_table
      .find_label(label_ref, current_idx)
      .map(|(_, id)| *id);
    id.and_then(move |id| self.table.get_mut(&SynthSymbol::Synth(id)))
  }
}

/// A table of digit labels.
///
/// Digit labels are labels like `1:`, which can occur many times throughout the
/// same assembly file, and can be referenced as `1f` or `1b`: the next or
/// previous label, in atom order, that has that digit.
///
/// This data structure works by remembering the location of each digit label
/// relative to some index (e.g. a line number), and supporting looking up the
/// closest digit label at a given position, forwards or backwards.
#[derive(Clone, Debug)]
pub struct DigitLabelTable<T> {
  /// The data structure is as follows: for each digit 0..=9, we have an entry
  /// in the array. For each digit value, we have the indices in a `File`'s atom
  /// list, which track where each label occured; a digit label reference is
  /// thus a list bisection.
  ///
  /// The pair itself is `(index, address)`.
  digits: [Vec<(usize, T)>; 10],
}

impl<T> DigitLabelTable<T> {
  /// Creates a new `DigitLabelTable`.
  pub fn new() -> Self {
    Self {
      digits: Default::default(),
    }
  }

  /// Defines a new digit label.
  ///
  /// The new label has digit `digit`, occuring at `atom_idx` and point to the
  /// value `x`.
  pub fn define(&mut self, digit: Digit, atom_idx: usize, x: T) {
    let digit_list = &mut self.digits[digit.into_inner() as usize];
    if let Some((last, _)) = digit_list.last() {
      assert!(atom_idx > *last)
    }
    digit_list.push((atom_idx, x))
  }

  /// Attempts to find a digit label definition.
  ///
  /// This function returns the value at the label defined at `atom_idx` with
  /// digit `digit`, if it exists.
  pub fn find_definition(&self, digit: Digit, atom_idx: usize) -> Option<&T> {
    let labels = &self.digits[digit.into_inner() as usize];
    if labels.is_empty() {
      return None;
    }

    match labels.binary_search_by(|(idx, _)| idx.cmp(&atom_idx)) {
      Ok(n) => Some(&labels[n].1),
      Err(_) => None,
    }
  }

  /// Attempts to find a digit label.
  ///
  /// The label searched for is one with digit `digit`, in either the forward,
  /// or backward, direction, relative to `current_idx`.
  pub fn find_label(
    &self,
    label_ref: DigitLabelRef,
    current_idx: usize,
  ) -> Option<&(usize, T)> {
    let labels = &self.digits[label_ref.digit.into_inner() as usize];
    if labels.is_empty() {
      return None;
    }

    let idx = match (
      label_ref.dir,
      labels.binary_search_by(|(idx, _)| idx.cmp(&current_idx)),
    ) {
      // This was a request to find this label relative to *itself*.
      (_, Ok(_)) => return None,
      // When we don't land exactly on an index, we get the "insertion point",
      // which is the index of the next biggest value, or the length of the
      // list, if there isn't one. Thus, for forwards, we return n, while for
      // backwards, we return n - 1. In both cases, we need to remove the
      // pathological cases: n = len, and n = 0.
      (Direction::Forward, Err(n)) => {
        if n == labels.len() {
          return None;
        } else {
          n
        }
      }
      (Direction::Backward, Err(n)) => {
        if n == 0 {
          return None;
        } else {
          n - 1
        }
      }
    };

    Some(&labels[idx])
  }
}
