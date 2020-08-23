//! The SNASM assembler, for converting assembly files into object files.

use std::fmt;

use crate::asm::dir::DirectiveType;
use crate::error;
use crate::int::u24;
use crate::int::Int;
use crate::int::Width;
use crate::isa::Instruction;
use crate::isa::Mnemonic;
use crate::obj;
use crate::obj::dbg;
use crate::obj::dbg::OffsetType;
use crate::obj::Object;
use crate::obj::Relocation;
use crate::obj::RelocationInfo;
use crate::obj::RelocationType;
use crate::syn::atom::Atom;
use crate::syn::atom::AtomType;
use crate::syn::code::AddrExpr;
use crate::syn::operand::LocalLabel;
use crate::syn::operand::Operand;
use crate::syn::operand::Symbol;
use crate::syn::src::Source;

mod dir;
mod tables;

/// Assembles the given assembly file.
///
/// Returns a complete `Object` on success, or a collection of `Error`s that may
/// have occured during assembly.
pub fn assemble<'atom, 'asm>(
  src: &'atom Source<'asm>,
) -> Result<Object<'asm>, error::Errors<Error<'atom, 'asm>>> {
  Assembler::new(src).run()
}

/// The main state struct for the assembler.
struct Assembler<'atom, 'asm> {
  /// The source file we're starting from
  src: &'atom Source<'asm>,
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
  errors: error::Errors<Error<'atom, 'asm>>,
}

#[derive(Copy, Clone)]
enum SymbolValue {
  Addr(u24),
  Bank(u8),
}

/// An error type, not including the `Atom` that caused it.
#[derive(Debug)]
pub enum ErrorType<'atom, 'asm> {
  /// Indicates an attempt to redefine an already-defined symbol.
  Redef(Symbol<'asm>, &'atom Atom<'asm>),
  /// Indicates that symbol resolution failed.
  UndefinedSymbol(Symbol<'asm>),
  /// Indicates that local label resolution failed.
  UndefinedLocal(LocalLabel),
  /// Indicates that the requested mnemonic, width, and addressing mode
  /// combination does not map to a real opcode.
  BadInstruction(Mnemonic, Option<AddrExpr<Int>>),
  /// Indicates that an integer is not of an appropriate width.
  BadIntType,
  /// Indicates failure to correctly parse some directive.
  BadDirective,
  /// Indicates that an instruction or directive was caught overflowing the
  /// current program bank.
  BankCrossing,
  /// Indicates that a symbol was too far away to be reached by a `pc`-relative
  /// instruction.
  SymbolTooFar(Symbol<'asm>),
  /// Indicates that a local label was too far away to be reached by a
  /// `pc`-relative instruction.
  LocalTooFar(LocalLabel),
}

/// An error produced during the assembly process.
#[derive(Debug)]
pub struct Error<'atom, 'asm> {
  /// The type of error.
  pub inner: ErrorType<'atom, 'asm>,
  /// The `Atom` at which the error was encountered.
  pub cause: &'atom Atom<'asm>,
  /// The `Source` that originated this error.
  pub source: &'atom Source<'asm>,
}

impl fmt::Display for Error<'_, '_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self.inner {
      ErrorType::Redef(sym, _) => write!(f, "redefinition of {}", sym),
      ErrorType::UndefinedSymbol(sym) => write!(f, "undefined symbol: {}", sym),
      ErrorType::UndefinedLocal(_) => write!(f, "undefined local"),
      ErrorType::BadInstruction(mne, _) => {
        write!(f, "invalid addressing mode for {}", mne)
      }
      ErrorType::BadIntType => write!(f, "bad integer type"),
      ErrorType::BadDirective => write!(f, "couldn't parse directive"),
      ErrorType::BankCrossing => write!(f, "tried to cross a bank boundary"),
      ErrorType::SymbolTooFar(sym) => {
        write!(f, "symbol too far for branch: {}", sym)
      }
      ErrorType::LocalTooFar(_) => write!(f, "local too far for branch"),
    }
  }
}

impl error::Error for Error<'_, '_> {
  fn cause(&self) -> error::Cause<'_> {
    match &self.cause.span {
      Some(span) => error::Cause::Span(span.clone()),
      None => error::Cause::File(self.source.file_name()),
    }
  }

  fn action(&self) -> Option<error::Action> {
    Some(error::Action::Assembling)
  }
}

/// Tracks the state of the DBR, the "Data Bank Register". By default, SNASM
/// will assume that DBR = PBR = `pc.bank`, but this behavior can be tweaked.
///
/// This is controlled by the `.bank` directive.
#[allow(unused)]
pub(in crate::asm) enum DbrState {
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
  instruction_offset: u16,
  expected_width: Width,
  arg_idx: usize,
  expected_bank: Option<u8>,

  source: SymOrLocal<'asm>,
  cause: &'atom Atom<'asm>,
}
#[derive(Copy, Clone)]
enum SymOrLocal<'asm> {
  Sym(Symbol<'asm>),
  Local(LocalLabel, usize),
}

const DEFAULT_PC: u24 = u24::from_u32(0x80_8000);

impl<'atom, 'asm: 'atom> Assembler<'atom, 'asm> {
  fn new(src: &'atom Source<'asm>) -> Self {
    Self {
      src,
      object: Object::new(src.file_name()),

      pc: DEFAULT_PC,
      dbr_state: DbrState::Pc,
      symbols: tables::SymbolTable::new(),
      references: Vec::new(),
      errors: error::Errors::new(),
    }
  }

  fn run(mut self) -> Result<Object<'asm>, error::Errors<Error<'atom, 'asm>>> {
    self.init_symbol_bank_table();
    if !self.errors.is_ok() {
      return Err(self.errors);
    }

    self.naive_assemble();
    if !self.errors.is_ok() {
      return Err(self.errors);
    }

    self.resolve_references();
    if !self.errors.is_ok() {
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
    for (idx, atom) in self.src.iter().enumerate() {
      match &atom.inner {
        AtomType::Label(sym) => {
          if let Err(old) =
            self
              .symbols
              .define(*sym, atom, SymbolValue::Bank(self.pc.bank))
          {
            self.errors.push(Error {
              inner: ErrorType::Redef(*sym, old),
              cause: atom,
              source: self.src,
            })
          }
        }
        AtomType::LocalLabel(digit) => self.symbols.define_local(
          *digit,
          idx,
          atom,
          SymbolValue::Bank(self.pc.bank),
        ),

        AtomType::Directive(d) => {
          let dir_ty = match DirectiveType::from_syn(d) {
            Some(d) => d,
            _ => {
              self.errors.push(Error {
                inner: ErrorType::BadDirective,
                cause: atom,
                source: self.src,
              });
              continue;
            }
          };

          match dir_ty {
            DirectiveType::Origin(value) => self.pc = value,
            DirectiveType::Extern { sym, bank } => {
              let bank = bank.unwrap_or(self.pc.bank);

              if let Err(old) =
                self.symbols.define(sym, atom, SymbolValue::Bank(bank))
              {
                self.errors.push(Error {
                  inner: ErrorType::Redef(sym, old),
                  cause: atom,
                  source: self.src,
                })
              }
            }
            _ => {}
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
    self.object.new_block(block_start);

    for (idx, atom) in self.src.iter().enumerate() {
      match &atom.inner {
        AtomType::Label(sym) => {
          self.object.get_block_mut(block_start).unwrap().add_label(dbg::Label::Symbol(dbg::Symbol {
            name: sym.name.into(),
            is_global: false,  // Debuginfo simplification will fix this up.
          }));
          self.symbols.lookup(*sym).unwrap().1 = SymbolValue::Addr(self.pc)
        }
        AtomType::LocalLabel(digit) => {
          self.object.get_block_mut(block_start).unwrap().add_label(dbg::Label::Local(digit.into_inner()));
          self.symbols.lookup_local_at_def(*digit, idx).unwrap().1 =
            SymbolValue::Addr(self.pc)
        }
        AtomType::Directive(d) => {
          let dir_ty = match DirectiveType::from_syn(&d) {
            Some(d) => d,
            _ => {
              self.errors.push(Error {
                inner: ErrorType::BadDirective,
                cause: atom,
                source: self.src,
              });
              continue;
            }
          };

          match dir_ty {
            DirectiveType::Origin(value) => {
              self.pc = value;
              // Because we've moved the program counter, we need to dump this block
              // and start building a new one.
              block_start = self.pc;
              self.object.new_block(block_start);
            }
            DirectiveType::Extern { .. } => {}
            DirectiveType::Global(sym) => {
              let &mut (_, val) = match self.symbols.lookup(sym) {
                Some(val) => val,
                _ => {
                  self.errors.push(Error {
                    inner: ErrorType::UndefinedSymbol(sym),
                    cause: atom,
                    source: self.src,
                  });
                  continue;
                }
              };
              let addr = match val {
                SymbolValue::Addr(addr) => addr,
                SymbolValue::Bank(_) => {
                  self.errors.push(Error {
                    inner: ErrorType::UndefinedSymbol(sym),
                    cause: atom,
                    source: self.src,
                  });
                  continue;
                }
              };

              self.object.define_global(sym, addr);
            }
            DirectiveType::Bank(dbr_state) => self.dbr_state = dbr_state,
            DirectiveType::Data { count, values } => {
              if count == 0 {
                continue;
              }
              let values = if values.is_empty() {
                &[Int::I8(0)][..]
              } else {
                &values[..]
              };

              let block = self.object.get_block_mut(block_start).unwrap();
              let mut data = block.begin_offset(OffsetType::Data);
              for _ in 0..count {
                for val in values {
                  let len = val.width().bytes() as u16;

                  self.pc.addr = match self.pc.addr.checked_add(len) {
                    Some(n) => n,
                    None => {
                      self.errors.push(Error {
                        inner: ErrorType::BankCrossing,
                        cause: atom,
                        source: self.src,
                      });
                      0u16
                    }
                  };
                  let _ = val.write_le(&mut data);
                }
              }
            }
          }
        }

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
              Operand::Int(int) => match inst.width {
                Some(width) => match int.value.zero_extend_checked(width) {
                  Some(val) => Ok(val),
                  None => Err(ErrorType::BadIntType),
                },
                _ => Ok(int.value),
              },

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
              Operand::Symbol(_) | Operand::Local(_) => {
                // Now, we compute the current bank, as is relevant to the
                // instruction being processed.
                let current_bank: Option<u8> = match self.dbr_state {
                  _ if inst.mnemonic.uses_pbr() => Some(self.pc.bank),
                  DbrState::Pc => Some(self.pc.bank),
                  DbrState::Else => None,
                  DbrState::Fixed(bank) => Some(bank),
                };

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
                    Operand::Local(local) => {
                      let entry = self.symbols.lookup_local(*local, idx);
                      match entry {
                        Some((_, addr)) => *addr,
                        _ => return Err(ErrorType::UndefinedLocal(*local)),
                      }
                    }
                    _ => unreachable!(),
                  };

                  let addr_bank = match addr_info {
                    SymbolValue::Bank(n) => n,
                    SymbolValue::Addr(n) => n.bank,
                  };

                  let width = if current_bank == Some(addr_bank) {
                    if inst.mnemonic.is_one_byte_branch() {
                      Width::I8
                    } else {
                      Width::I16
                    }
                  } else {
                    Width::I24
                  };
                  Ok(width)
                })?;

                let reloc_source = match arg {
                  Operand::Symbol(sym) => SymOrLocal::Sym(*sym),
                  Operand::Local(local) => SymOrLocal::Local(*local, idx),
                  _ => unreachable!(),
                };

                // Now, let's register a reference for this label.
                let block = self.object.get_block(block_start).unwrap();
                self.references.push(Reference {
                  block_id: block_start,
                  instruction_offset: block.len(),
                  expected_width: width,
                  expected_bank: current_bank,
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
                source: self.src,
              });
              continue;
            }
          };

          // There's no way we can accidentally zero-extend a label... I think.
          let instruction = match Instruction::build_from_with_zero_extension(
            inst.mnemonic,
            operand,
          ) {
            Some(i) => i,
            None => {
              self.errors.push(Error {
                inner: ErrorType::BadInstruction(inst.mnemonic, operand),
                cause: atom,
                source: self.src,
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
                  source: self.src,
                });
                0u16
              }
            };

          let block = self.object.get_block_mut(block_start).unwrap();
          let _ = instruction.write(block.begin_offset(OffsetType::Code));
        }
        AtomType::Empty => continue,
      }
    }
  }

  /// Resolves any references produced by the previous function, either by
  /// filling in data or by emitting relocations.
  fn resolve_references(&mut self) {
    for reference in &self.references {
      let block = self.object.get_block_mut(reference.block_id).unwrap();
      let inst_buf = &mut block[reference.instruction_offset..];
      let inst = Instruction::read(&*inst_buf).unwrap();

      // Every single operand is immediately after the first byte of the
      // instruction, except for the sole two-operand instructions mvn and mvp.
      // Since those are always one-byte operands, the second instruction offset
      // is on the *second* byte after.
      //
      // Also, we need to double-check: is the expected width equal to the
      // instruction length - 1? (For moves, it's (instruction length - 1) / 2.)
      // Failure of this assertion is always a bug.
      let destination_offset = reference.instruction_offset
        + if reference.arg_idx == 1
          && (inst.mnemonic() == Mnemonic::Mvn
            || inst.mnemonic() == Mnemonic::Mvp)
        {
          assert_eq!(reference.expected_width, Width::I8);
          2
        } else {
          assert_eq!(
            reference.expected_width.bytes(),
            inst.encoded_len() as u32 - 1
          );
          1
        };

      let (_, symbol_value) = match reference.source {
        SymOrLocal::Sym(sym) => self.symbols.lookup(sym),
        SymOrLocal::Local(local, idx) => self.symbols.lookup_local(local, idx),
      }
      .expect("all references are to valid symbols");

      let inst_end_offset =
        reference.instruction_offset as u16 + inst.encoded_len() as u16;
      let pc = reference.block_id + inst_end_offset;
      let relo_type = match reference.expected_width {
        Width::I16 if inst.mnemonic().is_pc_relative() => {
          RelocationType::AddrRelative16(pc)
        }
        Width::I8 if inst.mnemonic().is_pc_relative() => {
          RelocationType::AddrRelative8(pc)
        }
        Width::I24 => RelocationType::Absolute,
        Width::I16 => {
          RelocationType::BankRelative(reference.expected_bank.unwrap())
        }
        _ => unreachable!(),
      };

      let relocation = RelocationInfo {
        offset: destination_offset as u16,
        ty: relo_type,
      };

      let val = match (symbol_value, reference.source) {
        // Symbol was never completed; must be an external symbol.
        (SymbolValue::Bank(_), SymOrLocal::Sym(sym)) => {
          block.add_relocation(Relocation {
            info: relocation,
            source: sym,
          });
          continue;
        }
        // This should never happen. All local labels should have been resolved
        // by this point.
        (SymbolValue::Bank(_), SymOrLocal::Local(..)) => panic!(
          "local label reference was unresolved at the end of object assembly"
        ),
        (SymbolValue::Addr(addr), _) => addr,
      };

      match relocation.resolve_in(block, *val) {
        Ok(()) => {}
        Err(obj::RelocationError::SymbolTooFar) => match reference.source {
          SymOrLocal::Sym(sym) => self.errors.push(Error {
            inner: ErrorType::SymbolTooFar(sym),
            cause: reference.cause,
            source: self.src,
          }),
          SymOrLocal::Local(local, _) => self.errors.push(Error {
            inner: ErrorType::LocalTooFar(local),
            cause: reference.cause,
            source: self.src,
          }),
        },
        _ => unreachable!(),
      }
    }
  }
}
