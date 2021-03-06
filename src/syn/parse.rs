//! The SNASM parser.

use std::fmt;
use std::mem;
use std::path::Path;

use pest::error::Error as PestError;
use pest::error::InputLocation;
use pest::iterators::Pair;
use pest::Position;
use pest_derive::Parser;

pub use pest::Span as PestSpan;

use crate::error;
use crate::int::Int;
use crate::int::Width;
use crate::isa::Mnemonic;
use crate::syn::atom::Atom;
use crate::syn::atom::AtomType;
use crate::syn::atom::Directive;
use crate::syn::code::AddrExpr;
use crate::syn::code::Code;
use crate::syn::code::IdxReg;
use crate::syn::int::DigitStyle;
use crate::syn::int::IntLit;
use crate::syn::int::PrefixStyle;
use crate::syn::int::Unary;
use crate::syn::operand::Digit;
use crate::syn::operand::LocalLabel;
use crate::syn::operand::Operand;
use crate::syn::operand::Symbol;
use crate::syn::src::Comment;
use crate::syn::src::Source;
use crate::syn::src::Span;

#[derive(Parser)]
#[grammar = "syn/grammar.pest"]
struct PegParser;

/// A parsing error type.
#[derive(Clone, Debug)]
pub enum ErrorType<'asm> {
  /// An error originating from inside the PEG parser.
  Peg(PestError<Rule>),
  /// An error due to a bad integer.
  BadInt,
  /// An error due to a bad mnemonic.
  BadMnemonic(&'asm str),
}

impl From<PestError<Rule>> for ErrorType<'_> {
  fn from(e: PestError<Rule>) -> Self {
    ErrorType::Peg(e)
  }
}

/// A parsing error.
#[derive(Clone, Debug)]
pub struct Error<'asm> {
  /// The type of the error.
  pub inner: ErrorType<'asm>,
  /// The span at which the error occuyred.
  pub span: Span<'asm>,
}

impl fmt::Display for Error<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self.inner {
      ErrorType::Peg(..) => write!(f, "unknown syntax error"),
      ErrorType::BadInt => write!(f, "integer literal is invalid"),
      ErrorType::BadMnemonic(name) => {
        write!(f, "unknown instruction mnemonic: {}", name)
      }
    }
  }
}

impl error::Error for Error<'_> {
  fn cause(&self) -> error::Cause<'_> {
    error::Cause::Span(self.span.clone())
  }

  fn action(&self) -> Option<error::Action> {
    Some(error::Action::Parsing)
  }
}

/// Parse `src` into a SNASM file.
pub fn parse<'asm>(
  file_name: &'asm Path,
  src: &'asm str,
) -> Result<Source<'asm>, Error<'asm>> {
  let mut file = Source {
    name: file_name.into(),
    atoms: Vec::new(),
  };

  use pest::Parser;
  let mut pair = match PegParser::parse(Rule::File, src) {
    Ok(pair) => pair,
    Err(err) => {
      let span = match err.location {
        InputLocation::Pos(pos) => {
          let pos = Position::new(src, pos).unwrap();
          pos.span(&pos)
        }
        InputLocation::Span((start, end)) => {
          let start = Position::new(src, start).unwrap();
          let end = Position::new(src, end).unwrap();
          start.span(&end)
        }
      };
      let span = Span {
        name: file_name,
        span,
      };
      return Err(Error {
        inner: err.into(),
        span,
      });
    }
  };
  for line in pair.next().unwrap().into_inner() {
    let atoms = line.into_inner().collect::<Vec<_>>();
    let mut prev = Atom {
      inner: AtomType::Empty,
      comment: None,
      has_newline: false,
      span: None,
    };

    let len = file.atoms.len();
    for atom in atoms {
      let span = Some(Span {
        name: file_name,
        span: atom.as_span(),
      });
      match atom.as_rule() {
        Rule::Label => {
          let name = atom.into_inner().next().unwrap().as_str();

          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Label(Symbol { name }),
              comment: None,
              has_newline: false,
              span,
            },
          );
          file.atoms.push(prev);
        }
        Rule::DigitLabel => {
          let val = atom.as_str()[..1].parse().unwrap();
          let digit = Digit::new(val).unwrap();

          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::LocalLabel(digit),
              comment: None,
              has_newline: false,
              span,
            },
          );
          file.atoms.push(prev);
        }
        Rule::Directive => {
          let mut inner = atom.into_inner();
          let name = inner.next().unwrap().as_str();
          let mut args = Vec::new();
          for arg in inner {
            args.push(parse_operand(file_name, arg)?);
          }
          let directive = Directive {
            sym: Symbol { name },
            args,
          };
          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Directive(directive),
              comment: None,
              has_newline: false,
              span,
            },
          );
          file.atoms.push(prev);
        }
        Rule::Instruction => {
          let mut inner = atom.into_inner();

          let mne_str = inner.next().unwrap().as_str();
          let mut split = mne_str.split('.');
          let mne_name = split.next().unwrap();
          let mnemonic = Mnemonic::from_name(mne_name).ok_or(Error {
            inner: ErrorType::BadMnemonic(mne_name),
            span: span.clone().unwrap(),
          })?;
          let width = split.next().and_then(Width::from_name);

          let addr = inner
            .next()
            .map::<Result<AddrExpr<_>, Error<'asm>>, _>(|addr| {
              Ok(match addr.as_rule() {
                Rule::AddrAcc => AddrExpr::Acc,
                Rule::AddrImm => AddrExpr::Imm(parse_operand(
                  file_name,
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrAbs => AddrExpr::Abs(parse_operand(
                  file_name,
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrInd => AddrExpr::Ind(parse_operand(
                  file_name,
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrLongInd => AddrExpr::LongInd(parse_operand(
                  file_name,
                  addr.into_inner().next().unwrap(),
                )?),
                Rule::AddrIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(file_name, inner.next().unwrap())?;
                  let idx =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  AddrExpr::Idx(arg, idx)
                }
                Rule::AddrIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(file_name, inner.next().unwrap())?;
                  let idx =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  AddrExpr::IndIdx(arg, idx)
                }
                Rule::AddrIdxInd => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(file_name, inner.next().unwrap())?;
                  let idx =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  AddrExpr::IdxInd(arg, idx)
                }
                Rule::AddrIdxIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(file_name, inner.next().unwrap())?;
                  let idx =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  let idx2 =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  AddrExpr::IdxIndIdx(arg, idx, idx2)
                }
                Rule::AddrLongIndIdx => {
                  let mut inner = addr.into_inner();
                  let arg = parse_operand(file_name, inner.next().unwrap())?;
                  let idx =
                    IdxReg::from_str(inner.next().unwrap().as_str()).unwrap();
                  AddrExpr::LongIndIdx(arg, idx)
                }
                Rule::AddrMove => {
                  let mut inner = addr.into_inner();
                  let arg1 = parse_operand(file_name, inner.next().unwrap())?;
                  let arg2 = parse_operand(file_name, inner.next().unwrap())?;
                  AddrExpr::Move(arg1, arg2)
                }
                _ => unreachable!(),
              })
            })
            .transpose()?;

          let prev = mem::replace(
            &mut prev,
            Atom {
              inner: AtomType::Instruction(Code {
                mnemonic,
                width,
                addr,
              }),
              comment: None,
              has_newline: false,
              span,
            },
          );
          file.atoms.push(prev);
        }
        Rule::LineComment => {
          prev.comment = Some(Comment {
            text: atom.as_str(),
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
        ..
      })
    ) {
      file.atoms.remove(len);
    }
  }

  Ok(file)
}

fn parse_operand<'asm>(
  file_name: &'asm Path,
  operand: Pair<'asm, Rule>,
) -> Result<Operand<'asm>, Error<'asm>> {
  let span = Span {
    name: file_name,
    span: operand.as_span(),
  };
  match operand.as_rule() {
    Rule::IntDec | Rule::IntBin | Rule::IntHex => {
      let rule = operand.as_rule();
      let mut inner = operand.into_inner();
      let mut token = inner.next().unwrap();
      let unary = if token.as_rule() == Rule::IntOp {
        let unary = match token.as_str() {
          "-" => Some(Unary::Neg),
          "!" => Some(Unary::Not),
          _ => unreachable!(),
        };
        token = inner.next().unwrap();
        unary
      } else {
        None
      };

      let style = match rule {
        Rule::IntDec => DigitStyle::Dec,
        Rule::IntBin => {
          let style = if token.as_str() == "%" {
            PrefixStyle::Classic
          } else {
            PrefixStyle::Modern
          };
          token = inner.next().unwrap();
          DigitStyle::Bin(style)
        }
        Rule::IntHex => {
          let style = if token.as_str() == "$" {
            PrefixStyle::Classic
          } else {
            PrefixStyle::Modern
          };
          token = inner.next().unwrap();
          DigitStyle::Hex(style)
        }
        _ => unreachable!(),
      };

      let digits = token
        .as_str()
        .chars()
        .filter(|&c| c != '_')
        .collect::<String>();

      let value =
        u32::from_str_radix(&digits, style.radix()).map_err(|_| Error {
          inner: ErrorType::BadInt,
          span: span.clone(),
        })?;
      let width = inner
        .next()
        .and_then(|s| Width::from_name(s.as_str()))
        .or(Width::smallest_for(value))
        .ok_or_else(|| Error {
          inner: ErrorType::BadInt,
          span,
        })?;

      let mut value = Int::new(value, width);
      match unary {
        Some(Unary::Neg) => value = -value,
        Some(Unary::Not) => value = !value,
        _ => {}
      }

      Ok(Operand::Int(IntLit {
        value,
        unary,
        style,
      }))
    }
    Rule::Symbol => Ok(Operand::Symbol(Symbol {
      name: operand.as_str(),
    })),
    Rule::LabelRef => {
      let (value_str, dir) = operand.as_str().split_at(1);
      let value = value_str.parse().map_err(|_| Error {
        inner: ErrorType::BadInt,
        span,
      })?;
      let digit = Digit::new(value).unwrap();
      if dir == "f" {
        Ok(Operand::Local(LocalLabel::Forward(digit)))
      } else {
        Ok(Operand::Local(LocalLabel::Backward(digit)))
      }
    }
    _ => unreachable!(),
  }
}
