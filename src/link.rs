//! The linker, which is used to link several objects into a ROM.

#![allow(missing_docs)]
#![allow(unused)]

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;
use std::path::Path;

use crate::error;
use crate::int::u24;
use crate::obj;
use crate::obj::Object;
use crate::rom::Rom;
use crate::syn::operand::Symbol;

pub fn link<'asm>(
  rom: &mut dyn Rom,
  objects: &mut [Object<'asm>],
) -> Result<(), error::Errors<Error<'asm>>> {
  Linker::new(rom, objects).run()
}

#[derive(Debug)]
pub enum Error<'asm> {
  /// Indicates that two files have attempted to define the same symbol.
  DuplicateSymbol {
    /// The symbol that was duplicated.
    symbol: Symbol<'asm>,
    /// The name of the first file that tried to define it, if available.
    first: &'asm Path,
    /// The name of the second file that tried to define it, if available.
    second: &'asm Path,
  },
  /// Indicates that a symbol was requested, but never defined by any file.
  MissingSymbol {
    /// The symbol that was not defined.
    symbol: Symbol<'asm>,
    /// The file that requested the symbol.
    filename: &'asm Path,
  },
  /// Indicates a problem resolving a relocation.
  RelocationError {
    /// The file requesting the symbol.
    filename: &'asm Path,
    /// The symbol that was too far.
    symbol: Symbol<'asm>,
    /// The error itself.
    error: obj::RelocationError,
  },
  /// Indicates that two blocks overlap.
  BlockOverlap {
    /// The file and start of the first block.
    first: (&'asm Path, u24),
    /// The file and start of the second block.
    second: (&'asm Path, u24),
  },
  /// Indicates that a block tried to write to unmapped memory.
  Unmapped { filename: &'asm Path, addr: u24 },
}

impl fmt::Display for Error<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Error::DuplicateSymbol { symbol, first, .. } =>
        write!(f, "tried to redefine {}, first defined in {}",
          symbol, first.display()),
      Error::MissingSymbol { symbol, .. } =>
      write!(f, "definition not found for {}", symbol),
      Error::RelocationError {
        symbol,
        error: obj::RelocationError::WrongBank { expected, got },
        ..
      } => write!(f, "expected symbol in bank {:02}, found it in bank {:02}",
            expected, got),
      Error::RelocationError {
        symbol,
        error: obj::RelocationError::SymbolTooFar,
        ..
      } => write!(f, "symbol too far: {}", symbol),
      Error::BlockOverlap {
        first: (first_file, first_start),
        second: (second_file, second_start),
      } => write!(f, "blocks in {} starting at 0x{:06x} and in {} starting at 0x{:06x} overlap",
          first_file.display(), first_start,
          second_file.display(), second_start),
      Error::Unmapped { addr, .. } =>
        write!(f, "tried to write data to unmapped address 0x{:06x}", addr)
    }
  }
}

impl error::Error for Error<'_> {
  fn cause(&self) -> error::Cause<'_> {
    let path = match self {
      Error::DuplicateSymbol { second, .. } => second,
      Error::MissingSymbol { filename, .. } => filename,
      Error::RelocationError { filename, .. } => filename,
      Error::BlockOverlap {
        first: (filename, _),
        ..
      } => filename,
      Error::Unmapped { filename, .. } => filename,
    };
    error::Cause::File(path)
  }

  fn action(&self) -> Option<error::Action> {
    Some(error::Action::Linking)
  }
}

struct Linker<'asm, 'rom, 'obj> {
  rom: &'rom mut dyn Rom,
  objects: &'obj mut [Object<'asm>],

  errors: error::Errors<Error<'asm>>,
}

impl<'asm, 'rom, 'obj> Linker<'asm, 'rom, 'obj> {
  pub fn new(
    rom: &'rom mut dyn Rom,
    objects: &'obj mut [Object<'asm>],
  ) -> Self {
    Self {
      rom,
      objects,
      errors: error::Errors::new(),
    }
  }

  pub fn run(mut self) -> Result<(), error::Errors<Error<'asm>>> {
    self.resolve_relocations();
    if !self.errors.is_ok() {
      return Err(self.errors);
    }
    self.write_blocks();
    if !self.errors.is_ok() {
      return Err(self.errors);
    }

    Ok(())
  }

  fn resolve_relocations(&mut self) {
    let mut global_table = HashMap::<Symbol<'_>, (u24, &Path)>::new();

    for object in self.objects.iter() {
      for (symbol, addr) in object.globals() {
        match global_table.entry(symbol) {
          Entry::Occupied(entry) => {
            self.errors.push(Error::DuplicateSymbol {
              symbol,
              first: entry.get().1,
              second: object.file_name(),
            });
            continue;
          }
          e => e.or_insert((addr, object.file_name())),
        };
      }
    }

    for object in self.objects.iter_mut() {
      let name = object.file_name();
      for (_, block) in object.blocks_mut() {
        let relocations = block.relocations().copied().collect::<Vec<_>>();
        for relocation in relocations {
          let &(value, filename) = match global_table.get(&relocation.source) {
            Some(value) => value,
            None => {
              self.errors.push(Error::MissingSymbol {
                symbol: relocation.source,
                filename: name,
              });
              continue;
            }
          };

          if let Err(e) = relocation.info.resolve_in(block, value) {
            self.errors.push(Error::RelocationError {
              filename: name,
              symbol: relocation.source,
              error: e,
            })
          }
        }
      }
    }
  }

  fn write_blocks(&mut self) {
    // First, we need to make sure that none of the blocks overlap. We do so
    // by building a list of all the endpoints of all the blocks, sorting it,
    // and checking if any starts occur in a row.
    #[derive(Copy, Clone, Debug)]
    struct Endpoint<'a, 'b> {
      value: u24,
      is_start: bool,
      source: &'a Object<'b>,
    }

    let mut endpoints = Vec::new();
    for object in self.objects.iter() {
      for (start, block) in object.blocks() {
        if block.len() == 0 {
          continue;
        }
        let mut end = start;
        end.addr += block.len() as u16;
        endpoints.push(Endpoint {
          value: start,
          is_start: true,
          source: object,
        });
        endpoints.push(Endpoint {
          value: end,
          is_start: false,
          source: object,
        });
      }
    }

    endpoints.sort_by(|a, b| {
      a.value
        .cmp(&b.value)
        // Sort starts before ends. Recall that false < true.
        .then(b.is_start.cmp(&a.is_start))
    });

    let mut has_overlaps = false;
    for pair in endpoints.windows(2) {
      let first = pair[0];
      let second = pair[1];
      if first.is_start && second.is_start {
        has_overlaps = true;
        self.errors.push(Error::BlockOverlap {
          first: (first.source.file_name(), first.value),
          second: (second.source.file_name(), second.value),
        })
      }
    }

    if has_overlaps {
      return;
    }

    // Now we know that none of the blocks overlap. At last, we can lay out the
    // ROM.
    for object in self.objects.iter() {
      for (start, block) in object.blocks() {
        if let Err(addr) = self.rom.write(start, &block[..]) {
          self.errors.push(Error::Unmapped {
            filename: object.file_name(),
            addr,
          });
        }
      }
    }
  }
}
