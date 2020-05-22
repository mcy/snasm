//! The SNASM parser.

use std::mem;

use pest::error::Error as PestError;
use pest::iterators::Pair;
use pest_derive::Parser;

use crate::isa::Mnemonic;
use crate::syn::AddrExpr;
use crate::syn::Atom;
use crate::syn::AtomType;
use crate::syn::Comment;
use crate::syn::DigitStyle;
use crate::syn::File;
use crate::syn::IdxReg;
use crate::syn::Int;
use crate::syn::IntType;
use crate::syn::Operand;
use crate::syn::Symbol;

#[derive(Parser)]
#[grammar = "syn/grammar.pest"]
struct PegParser;

/// A parsing error.
#[derive(Clone, Debug)]
pub enum Error {
  /// An error originating from inside the PEG parser.
  Peg(PestError<Rule>),
  /// An error due to a bad integer.
  BadInt,
  /// An error due to a bad mnemonic.
  BadMnemonic,
  /// An error due to a bad register name.
  BadRegister,
}

impl From<PestError<Rule>> for Error {
  fn from(e: PestError<Rule>) -> Self {
    Error::Peg(e)
  }
}

/// Parse `src` into a SNASM file.
pub fn parse(file_name: &str, src: &str) -> Result<File, Error> {
  let mut file = File {
    name: file_name.into(),
    atoms: Vec::new(),
  };

  use pest::Parser;
  let mut pair = PegParser::parse(Rule::File, src)?;
  for line in pair.next().unwrap().into_inner() {
    let atoms = line.into_inner().collect::<Vec<_>>();
    let mut prev = Atom {
      inner: AtomType::Empty,
      comment: None,
      has_newline: false,
    };

    let len = file.atoms.len();
    for atom in atoms {
      match atom.as_rule() {
        Rule::Label => {
          let name = atom.into_inner().next().unwrap().as_str().into();

          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Label {
                name: Symbol { name },
              },
              comment: None,
              has_newline: false,
            },
          );
          file.atoms.push(prev);
        }
        Rule::Directive => {
          let mut inner = atom.into_inner();
          let name = inner.next().unwrap().as_str().into();
          let mut args = Vec::new();
          for arg in inner {
            if arg.as_rule() == Rule::Operand {
              args.push(parse_operand(arg)?);
            }
          }
          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Directive {
                name: Symbol { name },
                args,
              },
              comment: None,
              has_newline: false,
            },
          );
          file.atoms.push(prev);
        }
        Rule::Instruction => {
          let mut inner = atom.into_inner();
          let mne = Mnemonic::from_name(inner.next().unwrap().as_str())
            .ok_or(Error::BadMnemonic)?;
          let expr = inner
            .next()
            .map::<Result<AddrExpr, Error>, _>(|addr| {
              Ok(match addr.as_rule() {
                Rule::AddrAcc => AddrExpr::Acc,
                Rule::AddrImm => AddrExpr::Imm(parse_operand(
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrAbs => AddrExpr::Abs(parse_operand(
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrInd => AddrExpr::Ind(parse_operand(
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrLongInd => AddrExpr::LongInd(parse_operand(
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(inner.next().unwrap())?;
                  let idx = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  AddrExpr::Idx(arg, idx)
                }
                Rule::AddrIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(inner.next().unwrap())?;
                  let idx = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  AddrExpr::IndIdx(arg, idx)
                }
                Rule::AddrIdxInd => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(inner.next().unwrap())?;
                  let idx = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  AddrExpr::IdxInd(arg, idx)
                }
                Rule::AddrIdxIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(inner.next().unwrap())?;
                  let idx = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  let idx2 = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  AddrExpr::IdxIndIdx(arg, idx, idx2)
                }
                Rule::AddrLongIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(inner.next().unwrap())?;
                  let idx = IdxReg::from_str(inner.next().unwrap().as_str())
                    .ok_or(Error::BadRegister)?;
                  AddrExpr::LongIndIdx(arg, idx)
                }
                _ => unreachable!(),
              })
            })
            .transpose()?;

          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Instruction { mne, expr },
              comment: None,
              has_newline: false,
            },
          );
          file.atoms.push(prev);
        }
        Rule::LineComment => {
          prev.comment = Some(Comment {
            text: atom.as_str().into(),
          })
        }
        _ => unreachable!(),
      }
    }

    prev.has_newline = true;
    file.atoms.push(prev);

    if matches!(
      file.atoms.get(len),
      Some(Atom {
        inner: AtomType::Empty,
        comment: None,
        has_newline: false,
      })
    ) {
      file.atoms.remove(len);
    }
  }

  Ok(file)
}

fn parse_operand(operand: Pair<Rule>) -> Result<Operand, Error> {
  match operand.as_rule() {
    Rule::IntDec => {
      let is_negative = operand.as_str().starts_with("-");
      let mut inner = operand.into_inner();
      let first = inner.next().unwrap();

      let mut value =
        i32::from_str_radix(first.as_str(), 10).map_err(|_| Error::BadInt)?;
      if is_negative {
        value = -value;
      }

      let ty = inner
        .next()
        .and_then(|s| IntType::from_str(s.as_str()))
        .or(IntType::smallest_for(value))
        .ok_or(Error::BadInt)?;
      Ok(Operand::Int(Int {
        value,
        ty,
        style: DigitStyle::Dec,
      }))
    }
    Rule::IntBin => {
      let mut inner = operand.into_inner();
      let first = inner.next().unwrap().as_str();

      let value = i32::from_str_radix(first, 2).map_err(|_| Error::BadInt)?;
      let ty = inner
        .next()
        .and_then(|s| IntType::from_str(s.as_str()))
        .or(IntType::smallest_for(value))
        .ok_or(Error::BadInt)?;
      Ok(Operand::Int(Int {
        value,
        ty,
        style: DigitStyle::Bin,
      }))
    }
    Rule::IntHex => {
      let mut inner = operand.into_inner();
      let first = inner.next().unwrap().as_str();

      let value = i32::from_str_radix(first, 16).map_err(|_| Error::BadInt)?;
      let ty = inner
        .next()
        .and_then(|s| IntType::from_str(s.as_str()))
        .or(IntType::smallest_for(value))
        .ok_or(Error::BadInt)?;
      Ok(Operand::Int(Int {
        value,
        ty,
        style: DigitStyle::Hex,
      }))
    }
    Rule::Symbol => Ok(Operand::Symbol(Symbol {
      name: operand.as_str().into(),
    })),
    Rule::LabelRef => {
      let (value_str, dir) = operand.as_str().split_at(1);
      let value = value_str.parse().map_err(|_| Error::BadInt)?;
      let is_forward = dir == "f";
      Ok(Operand::LabelRef { value, is_forward })
    }
    _ => unreachable!(),
  }
}
