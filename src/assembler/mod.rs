//! The SNASM assembler, for converting assembly files into object files.

use std::collections::HashMap;
use std::convert::TryInto;
use std::io;

use crate::int::u24;
use crate::int::Int;
use crate::int::Width;
use crate::isa::Instruction;
use crate::isa::Mnemonic;
use crate::syn::AddrExpr;
use crate::syn::Atom;
use crate::syn::AtomType;
use crate::syn::DigitLabelRef;
use crate::syn::Directive;
use crate::syn::DirectiveType;
use crate::syn::File;
use crate::syn::Operand;
use crate::syn::Symbol;
use crate::syn::fmt;

mod tables;

/// An assembled object file.
///
/// An `Object` is made up of a collection of `Block`s, each of which starts at
/// a different 24-bit address.
pub struct Object<'asm> {
  blocks: HashMap<u24, Block<'asm>>,
}

impl<'asm> Object<'asm> {
  /// Creates a new, empty `Object`.
  pub fn new() -> Self {
    Object {
      blocks: HashMap::new(),
    }
  }

  /// Dumps this object in the style of `objdump` to `w`.
  pub fn dump(&self, mut w: impl io::Write) -> io::Result<()> {
    for (addr, block) in &self.blocks {
      writeln!(w, ".origin 0x{:06x}", addr)?;
      for i in 0..block.inst_offsets.len() {
        let start = block.inst_offsets[i];
        let end = block
          .inst_offsets
          .get(i + 1)
          .copied()
          .unwrap_or(block.data.len());

        let expected_len = (end - start) * 4;
        let padding = 16 - expected_len;

        write!(w, "{:06x}:", addr.to_u32() + start as u32)?;
        for j in start..end {
          write!(w, "  {:02x}", block.data[j])?;
        }

        for _ in 0..padding {
          write!(w, " ")?;
        }
        if let Ok(instruction) = Instruction::read(&block.data[start..]) {
          fmt::print_instruction(&fmt::Options::default(), instruction, &mut w)?
        }

        writeln!(w, "")?;
      }

      for relocation in &block.relocations {
        writeln!(
          w,
          ".reloc.{} 0x{:04x} {}",
          relocation.destination_width,
          relocation.instruction_offset,
          relocation.source.name
        )?;
      }
      writeln!(w, "")?;
    }

    Ok(())
  }
}

/// A block of assembled data.
///
/// A `Block` is a chunk of assmbled data, potentially requiring relocations
/// to be complete. Each `Block` roughly corresponds to an `.origin` directive.
pub struct Block<'asm> {
  data: Vec<u8>,
  inst_offsets: Vec<usize>,
  relocations: Vec<Relocation<'asm>>,
}

impl<'asm> Block<'asm> {
  /// Creates a new, empty `Block`.
  pub fn new() -> Self {
    Block {
      data: Vec::new(),
      inst_offsets: Vec::new(),
      relocations: Vec::new(),
    }
  }

  /// Marks the next index as the begining of an instruction.
  fn push_instruction_marker(&mut self) {
    self.inst_offsets.push(self.data.len())
  }

  /// Returns the length of this block.
  fn len(&self) -> usize {
    self.data.len()
  }
}

/// A relocation for a missing symbol.
///
/// A `Relocation` describes information that's missing from an assembled
/// `Block`, which can be filled in by a linker.
pub struct Relocation<'asm> {
  /// An offset into the containing block indicating where the instruction
  /// targeted by this relocation is located.
  pub instruction_offset: u16,
  /// An offset into the containing block poing to the exact place where the
  /// symbol value needs to be written.
  pub destination_offset: u16,
  /// The width of the destination: how many bytes need to be actually written.
  pub destination_width: Width,
  /// The symbol that is needed to resolve this relocation.
  pub source: Symbol<'asm>,
}

/// Assembles the given assembly file.
///
/// Returns a complete `Object` on success, or a collection of `Error`s that may
/// have occured during assembly.
pub fn assemble<'atom, 'asm>(file: &'atom File<'asm>) -> Result<Object<'asm>, Vec<Error<'atom, 'asm>>> {
  Assembler::new(file).run()
}

/// The main state struct for the assembler.
struct Assembler<'atom, 'asm> {
  /// The source file we're starting from
  file: &'atom File<'asm>,
  /// The object file being assembled.
  object: Object<'asm>,

  /// The current program counter.
  pc: u24,
  /// The state of the DBR. This state can be changed by assembler directives,
  /// to control how labels are optimized.
  dbr_state: DbrState,
  /// The symbol table for this file.
  symbols: tables::SymbolTable<'atom, 'asm, SymbolValue>,
  /// A list of references to symbols that need to be resolved before assembly
  /// is finished, either by finding them in the current file or by emitting
  /// relocation entries.
  references: Vec<Reference<'atom, 'asm>>,

  /// Errors generated during various phases of assembly.
  errors: Vec<Error<'atom, 'asm>>,
}

#[derive(Copy, Clone)]
enum SymbolValue {
  Addr(u24),
  Bank(u8),
}

/// An error type, not including the `Atom` that caused it.
#[derive(Debug)]
pub enum ErrorType<'atom, 'asm> {
  /// Something bad but unspecified occured.
  Unknown,
  /// Indicates an attempt to redefine an already-defined symbol.
  Redef(Symbol<'asm>, &'atom Atom<'asm>),
  /// Indicates that symbol resolution failed.
  UndefinedSymbol(Symbol<'asm>),
  /// Indicates that digit label resolution failed.
  UndefinedDigitLabel(DigitLabelRef),
  /// Indicates that the requested mnemonic, width, and addressing mode
  /// combination does not map to a real opcode.
  BadInstruction(Mnemonic, Option<AddrExpr<Int>>),
  /// Indicates that an integer is not of an appropriate width.
  BadIntType,
  /// Indicates that an instruction or directive was caught overflowing the
  /// current program bank.
  BankCrossing,
  /// Indicates that a symbol was too far away to be reached by a `pc`-relative
  /// instruction.
  SymbolTooFar(Symbol<'asm>),
  /// Indicates that a digit label was too far away to be reached by a
  /// `pc`-relative instruction.
  DigitTooFar(DigitLabelRef),
}

/// An error produced during the assembly process.
#[derive(Debug)]
pub struct Error<'atom, 'asm> {
  /// The type of error.
  pub inner: ErrorType<'atom, 'asm>,
  /// The `Atom` at which the error was encountered.
  pub cause: &'atom Atom<'asm>,
}

/// Tracks the state of the DBR, the "Data Bank Register". By default, SNASM
/// will assume that DBR = PBR = `pc.bank`, but this behavior can be tweaked.
///
/// This is controlled by the `.bank` directive.
#[allow(unused)]
enum DbrState {
  /// Assume that the DBR tracks the PC.
  Pc,
  /// Assume that the DBR is somewhere completely different, maximally
  /// pessimizing label layout.
  Else,
  /// Assume the DBR is in some other, specific bank.
  Fixed(u8),
}

/// A `Reference` indicates that some code used a symbolic value as one of
/// its operands. Whenever this happens, label optimization tries to guess
/// the smallest valid width for the reference, and fills that space with
/// zeroes.
///
/// Label optimization works as follows:
/// - If an instruction specifies an operand width, the label is truncated
///   to that (for examble, DP access *must* use .i8 when used with a
///   label).
/// - If that's not available, we use the label's bank (we know the banks
///   of all labels a-priori) to determine whether we can contract it to a
///   same-bank label; this depends on the value of the PBR/DBR. The DBR is
///   assumed to track the PBR, unless the user changes this fact.
/// - If we don't know the bank, we would have to assume a full i24 label,
///   or that it's in the current bank (both of which are reasonable
///   choices).
///   This is currently not supported but may be in the future.
///
/// At the end, we need to process all of the references by either fixing up
/// existing code, or emitting relocations.
struct Reference<'atom, 'asm> {
  block_id: u24,
  instruction_offset: usize,
  expected_width: Width,
  arg_idx: usize,

  source: SymOrDlr<'asm>,
  cause: &'atom Atom<'asm>,
}
#[derive(Copy, Clone)]
enum SymOrDlr<'asm> {
  Sym(Symbol<'asm>),
  Dlr(DigitLabelRef, usize),
}

const DEFAULT_PC: u24 = u24::from_u32(0x80_8000);

impl<'atom, 'asm: 'atom> Assembler<'atom, 'asm> {
  fn new(file: &'atom File<'asm>) -> Self {
    Self {
      file,
      object: Object::new(),

      pc: DEFAULT_PC,
      dbr_state: DbrState::Pc,
      symbols: tables::SymbolTable::new(),
      references: Vec::new(),
      errors: Vec::new(),
    }
  }

  fn run(mut self) -> Result<Object<'asm>, Vec<Error<'atom, 'asm>>> {
    self.init_symbol_bank_table();
    if !self.errors.is_empty() {
      return Err(self.errors);
    }

    self.naive_assemble();
    if !self.errors.is_empty() {
      return Err(self.errors);
    }

    self.resolve_references();
    if !self.errors.is_empty() {
      return Err(self.errors);
    }

    Ok(self.object)
  }

  /// Resets the program counter (and accociated values) to their default state.
  ///
  /// This function is useful to call when completing a phase of linear
  /// analysis, such as discovering information about all the labels.
  fn reset_pc(&mut self) {
    self.pc = DEFAULT_PC;
    self.dbr_state = DbrState::Pc;
  }

  /// Builds the initial symbol table via a simplistic traversal of labels and
  /// directives.
  fn init_symbol_bank_table(&mut self) {
    for (idx, atom) in self.file.atoms.iter().enumerate() {
      match atom.inner {
        AtomType::Label(sym) => {
          if let Err(old) =
            self
              .symbols
              .define(sym, atom, SymbolValue::Bank(self.pc.bank))
          {
            self.errors.push(Error {
              inner: ErrorType::Redef(sym, old),
              cause: atom,
            })
          }
        }
        AtomType::DigitLabel(digit) => self.symbols.define_digit(
          digit,
          idx,
          atom,
          SymbolValue::Bank(self.pc.bank),
        ),

        AtomType::Directive(Directive {
          ty: DirectiveType::Origin(int),
          ..
        }) => {
          let value = u24::from_u32(int.value.to_u32());
          self.pc = value;
        }

        AtomType::Directive(Directive {
          ty: DirectiveType::Extern { sym, bank },
          ..
        }) => {
          let bank = match bank {
            Some(int) => match int.value {
              Int::I8(bank) => bank,
              _ => {
                self.errors.push(Error {
                  inner: ErrorType::BadIntType,
                  cause: atom,
                });
                continue;
              }
            },
            None => self.pc.bank,
          };

          if let Err(old) =
            self.symbols.define(sym, atom, SymbolValue::Bank(bank))
          {
            self.errors.push(Error {
              inner: ErrorType::Redef(sym, old),
              cause: atom,
            })
          }
        }
        _ => continue,
      }
    }

    self.reset_pc();
  }

  /// Performs a first pass, "naive" assembly, which does most of the legwork of
  /// converting instructions into bytes. It will generate references to be
  /// resolved into relocations later on.
  fn naive_assemble(&mut self) {
    let mut block_start = self.pc;
    self.object.blocks.insert(block_start, Block::new());

    for (idx, atom) in self.file.atoms.iter().enumerate() {
      match &atom.inner {
        AtomType::Label(sym) => {
          self.symbols.lookup(*sym).unwrap().1 = SymbolValue::Addr(self.pc)
        }
        AtomType::DigitLabel(digit) => {
          self.symbols.lookup_digit_at_def(*digit, idx).unwrap().1 =
            SymbolValue::Addr(self.pc)
        }

        AtomType::Directive(Directive {
          ty: DirectiveType::Origin(int),
          ..
        }) => {
          let value = u24::from_u32(int.value.to_u32());
          self.pc = value;

          // Because we've moved the program counter, we need to dump this block
          // and start building a new one.
          block_start = self.pc;
          self.object.blocks.insert(block_start, Block::new());
        }
        AtomType::Directive(..) => continue,

        AtomType::Instruction(inst) => {
          // First, we need to resolve operands into integers.
          let maybe_operand = match &inst.addr {
            Some(addr) => Some(addr.map(|arg_idx, arg| match arg {
              // We need to try to squeeze whatever `arg` resolves to one of the
              // three integer types.
              // - If the instruction specifies a width like .i16, we make sure
              //   that the integer we've been given fits in there; otherwise,
              //   it's an error.
              // - In all other cases we just use the existing integer.
              Operand::Int(int) => {
                if inst.width.is_none() || inst.width == Some(int.value.width())
                {
                  Ok(int.value)
                } else {
                  Err(ErrorType::BadIntType)
                }
              }

              // For symbols, we need to generate a relocation. To do so, we
              // need to know
              // - The symbol has already been defined in the file, so we can
              //   just use it as-is.
              // - The symbol's bank is known, either due to being defined
              //   further down in the file (and, thus, its exact value depends
              //   on the widths of upcoming instructions), or due to an extern.
              //   In this case, we use the pc + dbr state to deduce wether the
              //   bank is implicit or not, and put in a relocation.
              // - We've never seen this symbol before. This is an error.
              Operand::Symbol(_) | Operand::DigitLabelRef { .. } => {
                let width = inst.width.map(Ok).unwrap_or_else(|| {
                  // First, we pull whatever address information we can out of
                  // the symbol table.
                  let addr_info = match arg {
                    Operand::Symbol(sym) => {
                      let entry = self.symbols.lookup(*sym);
                      match entry {
                        Some((_, addr)) => *addr,
                        _ => return Err(ErrorType::UndefinedSymbol(*sym)),
                      }
                    }
                    Operand::DigitLabelRef(dlr) => {
                      let entry = self.symbols.lookup_digit(*dlr, idx);
                      match entry {
                        Some((_, addr)) => *addr,
                        _ => return Err(ErrorType::UndefinedDigitLabel(*dlr)),
                      }
                    }
                    _ => unreachable!(),
                  };

                  let addr_bank = match addr_info {
                    SymbolValue::Bank(n) => n,
                    SymbolValue::Addr(n) => n.bank,
                  };

                  // Now, we compute the current bank, as is relevant to the
                  // instruction being processed.
                  let current_bank: Option<u8> = match self.dbr_state {
                    _ if inst.mne.uses_pbr() => Some(self.pc.bank),
                    DbrState::Pc => Some(self.pc.bank),
                    DbrState::Else => None,
                    DbrState::Fixed(bank) => Some(bank),
                  };

                  if current_bank == Some(addr_bank) {
                    if inst.mne.is_one_byte_branch() {
                      Ok(Width::I8)
                    } else {
                      Ok(Width::I16)
                    }
                  } else {
                    Ok(Width::I24)
                  }
                })?;

                let reloc_source = match arg {
                  Operand::Symbol(sym) => SymOrDlr::Sym(*sym),
                  Operand::DigitLabelRef(dlr) => SymOrDlr::Dlr(*dlr, idx),
                  _ => unreachable!(),
                };

                // Now, let's register a reference for this label.
                let block = &self.object.blocks[&block_start];
                self.references.push(Reference {
                  block_id: block_start,
                  instruction_offset: block.len(),
                  expected_width: width,
                  arg_idx,
                  source: reloc_source,
                  cause: atom,
                });

                Ok(Int::new(0, width))
              }
              _ => unreachable!(),
            })),
            None => None,
          };

          let operand = match maybe_operand.transpose() {
            Ok(o) => o,
            Err(e) => {
              self.errors.push(Error {
                inner: e,
                cause: atom,
              });
              continue;
            }
          };

          let instruction = match Instruction::build_from(inst.mne, operand) {
            Some(i) => i,
            None => {
              self.errors.push(Error {
                inner: ErrorType::BadInstruction(inst.mne, operand),
                cause: atom,
              });
              continue;
            }
          };

          self.pc.addr =
            match self.pc.addr.checked_add(instruction.encoded_len() as u16) {
              Some(n) => n,
              None => {
                self.errors.push(Error {
                  inner: ErrorType::BankCrossing,
                  cause: atom,
                });
                0u16
              }
            };

          let block = self.object.blocks.get_mut(&block_start).unwrap();
          block.push_instruction_marker();
          let _ = instruction.write(&mut block.data);
        }
        AtomType::Empty => continue,
      }
    }
  }

  /// Resolves any references produced by the previous function, either by
  /// filling in data or by emitting relocations.
  fn resolve_references(&mut self) {
    for reference in &self.references {
      let block = self.object.blocks.get_mut(&reference.block_id).unwrap();
      let inst_buf = &mut block.data[reference.instruction_offset..];
      let inst = Instruction::read(&*inst_buf).unwrap();

      // Every single operand is immediately after the first byte of the
      // instruction, except for the sole two-operand instructions mvn and mvp.
      // Since those are always one-byte operands, the second instruction offset
      // is on the *second* byte after.
      let destination_offset = reference.instruction_offset
        + if reference.arg_idx == 1
          && (inst.mnemonic() == Mnemonic::Mvn
            || inst.mnemonic() == Mnemonic::Mvp)
        {
          2
        } else {
          1
        };

      let &mut (_, symbol_value) = match reference.source {
        SymOrDlr::Sym(sym) => self.symbols.lookup(sym),
        SymOrDlr::Dlr(dlr, idx) => self.symbols.lookup_digit(dlr, idx),
      }
      .expect("all references are to valid symbols");

      let val = match (symbol_value, reference.source) {
        // Symbol was never completed; must be an external symbol.
        (SymbolValue::Bank(_), SymOrDlr::Sym(sym)) => {
          block.relocations.push(Relocation {
            instruction_offset: reference.instruction_offset as u16,
            destination_offset: destination_offset as u16,
            destination_width: reference.expected_width,
            source: sym,
          });
          continue;
        }
        // This should never happen. All digit labels should have been resolved
        // by this point.
        (SymbolValue::Bank(_), SymOrDlr::Dlr(..)) => panic!(
          "digit symbol reference was unresolved at the end of object assembly"
        ),
        (SymbolValue::Addr(addr), _) => addr,
      };

      // Note: all pc-relative instructions at i16 or smaller.
      // At this point, know for a fact that `val` is in the same bank.
      if inst.mnemonic().is_pc_relative() {
        let mut next_pc = reference.block_id.addr;
        next_pc = next_pc.wrapping_add(reference.instruction_offset as u16);
        next_pc = next_pc.wrapping_add(inst.encoded_len() as u16);

        let offset = val.addr.wrapping_sub(next_pc) as i16;
        if inst.mnemonic().is_one_byte_branch() {
          let offset: i8 = match offset.try_into() {
            Ok(offset) => offset,
            _ => {
              match reference.source {
                SymOrDlr::Sym(sym) => self.errors.push(Error {
                  inner: ErrorType::SymbolTooFar(sym),
                  cause: reference.cause,
                }),
                SymOrDlr::Dlr(dlr, _) => self.errors.push(Error {
                  inner: ErrorType::DigitTooFar(dlr),
                  cause: reference.cause,
                }),
              }
              continue;
            }
          };

          inst_buf[1] = offset as u8;
        } else {
          inst_buf[..2].copy_from_slice(&offset.to_le_bytes());
        }
        continue
      }
      // All the awful cases have been dealt with. We can just truncate val if
      // necessary and write it to the destination.
      let int = Int::new(val.to_u32(), reference.expected_width);
      int
        .write_le(&mut block.data[destination_offset..])
        .expect("the space being overwritten should already be zeroed")
    }
  }
}