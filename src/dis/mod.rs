//! The SNASM disassembler, for dismantling object files into source files.

use std::mem;

use crate::isa::Instruction;
use crate::obj::dbg;
use crate::obj::Object;
use crate::syn::atom::Atom;
use crate::syn::atom::AtomType;
use crate::syn::atom::Directive;
use crate::syn::code::Code;
use crate::syn::int::DigitStyle;
use crate::syn::int::IntLit;
use crate::syn::int::PrefixStyle;
use crate::syn::operand::Digit;
use crate::syn::operand::Operand;
use crate::syn::src::Source;

/// Disassembles `obj` using whatever debug information is present inside it.
pub fn disassemble<'asm>(obj: &'asm Object<'asm>) -> Source<'asm> {
  let mut src = Source::empty(obj.file_name());

  for (start, block) in obj.blocks() {
    // Push `.origin start` to start the block.
    src.add_atom(Atom {
      inner: AtomType::Directive(Directive {
        sym: ".origin".into(),
        args: vec![Operand::Int(IntLit {
          value: start.into(),
          unary: None,
          style: DigitStyle::Hex(PrefixStyle::Classic),
        })],
      }),
      comment: None,
      has_newline: true,
      span: None,
    });

    for offset in block.offsets() {
      let end = offset.start + offset.len;
      let bytes = &block[offset.start..end];
      match offset.ty {
        dbg::OffsetType::Code => {
          let mut block_offset = offset.start;
          for instruction in Instruction::stream(bytes) {
            let instruction = instruction.unwrap();
            for attr in block.attrs_at(block_offset) {
              let atom = match attr {
                dbg::Attr::Label(dbg::Label::Symbol(sym)) => {
                  AtomType::Label(sym.into())
                }
                dbg::Attr::Label(dbg::Label::Local(digit)) => {
                  AtomType::LocalLabel(Digit::new(*digit).unwrap())
                }
              };
              src.add_atom(Atom {
                inner: atom,
                comment: None,
                has_newline: true,
                span: None,
              });
              if let dbg::Attr::Label(dbg::Label::Symbol(dbg::Symbol {
                name,
                is_global: true,
              })) = attr
              {
                src.add_atom(Atom {
                  inner: AtomType::Directive(Directive {
                    sym: ".global".into(),
                    args: vec![Operand::Symbol(name.into())],
                  }),
                  comment: None,
                  has_newline: true,
                  span: None,
                });
              }
            }

            let code = Code {
              mnemonic: instruction.mnemonic(),
              width: None,
              addr: instruction.addressing_mode().map(|addr| {
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

            src.add_atom(Atom {
              inner: AtomType::Instruction(code),
              comment: None,
              has_newline: true,
              span: None,
            });

            block_offset += instruction.encoded_len() as u16;
          }
        }
        dbg::OffsetType::Data => {
          let mut byte_literals = Vec::new();
          for (idx, byte) in bytes.iter().cloned().enumerate() {
            let block_offset = offset.start + idx as u16;

            for attr in block.attrs_at(block_offset) {
              if !byte_literals.is_empty() {
                src.add_atom(Atom {
                  inner: AtomType::Directive(Directive {
                    sym: ".data".into(),
                    args: mem::take(&mut byte_literals),
                  }),
                  comment: None,
                  has_newline: true,
                  span: None,
                });
              }

              let atom = match attr {
                dbg::Attr::Label(dbg::Label::Symbol(sym)) => {
                  AtomType::Label(sym.into())
                }
                dbg::Attr::Label(dbg::Label::Local(digit)) => {
                  AtomType::LocalLabel(Digit::new(*digit).unwrap())
                }
              };
              src.add_atom(Atom {
                inner: atom,
                comment: None,
                has_newline: true,
                span: None,
              });
              if let dbg::Attr::Label(dbg::Label::Symbol(dbg::Symbol {
                name,
                is_global: true,
              })) = attr
              {
                src.add_atom(Atom {
                  inner: AtomType::Directive(Directive {
                    sym: ".global".into(),
                    args: vec![Operand::Symbol(name.into())],
                  }),
                  comment: None,
                  has_newline: true,
                  span: None,
                });
              }
            }

            byte_literals.push(Operand::Int(IntLit {
              value: byte.into(),
              unary: None,
              style: DigitStyle::Hex(PrefixStyle::Classic),
            }));

            if byte_literals.len() == 16 {
              src.add_atom(Atom {
                inner: AtomType::Directive(Directive {
                  sym: ".data".into(),
                  args: mem::take(&mut byte_literals),
                }),
                comment: None,
                has_newline: true,
                span: None,
              });
            }
          }

          if !byte_literals.is_empty() {
            src.add_atom(Atom {
              inner: AtomType::Directive(Directive {
                sym: ".data".into(),
                args: mem::take(&mut byte_literals),
              }),
              comment: None,
              has_newline: true,
              span: None,
            });
          }
        }
      }
    }
  }

  src
}
