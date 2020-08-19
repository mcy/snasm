//! Assembler directive handling.

use crate::asm::DbrState;
use crate::int::u24;
use crate::int::Int;
use crate::syn::atom::Directive;
use crate::syn::int::IntLit;
use crate::syn::operand::Operand;
use crate::syn::operand::Symbol;

/// A directive type, indicating a well-known assembler directive.
pub(in crate::asm) enum DirectiveType<'asm> {
  /// The `.origin` directive, indicating to the assembler that the program
  /// counter should unconditionally jump to the given argument.
  Origin(u24),
  /// The `.extern` directive, which indicates that a name is defined in another
  /// file. If the bank the symbol is allocated in is not given, it is assumed
  /// to be in the current bank.
  Extern {
    /// The external symbol name.
    sym: Symbol<'asm>,
    /// The bank, if different from the current one.
    bank: Option<u8>,
  },
  /// The `.global` directive, which marks a symbol as exported from the current
  /// file, usable in `.extern` directives elsewhere. It must appear after the
  /// label is defined.
  Global(Symbol<'asm>),
  /// The `.bank auto` directive, which changes the DBR state known to the
  /// assembler.
  Bank(DbrState),
  /// A generic directive for emitting straight literal data. `.data`, `.fill`,
  /// and `.zero` are sugar for this directive.
  Data {
    /// The number of bytes to fill with.
    count: usize,
    /// The value to fill the region with. If empty, this is treated as if it
    /// were a single, zero byte.
    values: Vec<Int>,
  },
}

impl<'asm> DirectiveType<'asm> {
  /// Parses a well-known directive from the given syntax.
  ///
  /// This function also handles directive synonyms, reducing them down to
  /// something simple that the assembler can understand.
  // TODO: A better error type?
  pub fn from_syn(dir: &Directive<'asm>) -> Option<Self> {
    let name = dir.sym.name.to_lowercase();
    let dir = match name.as_str() {
      ".origin" | ".org" => match &dir.args[..] {
        [Operand::Int(int)] => {
          DirectiveType::Origin(u24::from_u32(int.value.to_u32()))
        }
        _ => return None,
      },
      ".extern" => match &dir.args[..] {
        [Operand::Symbol(sym)] => DirectiveType::Extern {
          sym: *sym,
          bank: None,
        },
        [Operand::Symbol(sym), Operand::Int(IntLit {
          value: Int::I8(bank),
          ..
        })] => DirectiveType::Extern {
          sym: *sym,
          bank: Some(*bank),
        },
        _ => return None,
      },
      ".bank" => match &dir.args[..] {
        [Operand::Symbol(Symbol { name, .. })] => match *name {
          "auto" | "pc" => DirectiveType::Bank(DbrState::Pc),
          "no_assume" | "else" | "unknown" => {
            DirectiveType::Bank(DbrState::Else)
          }
          _ => return None,
        },
        [Operand::Int(IntLit {
          value: Int::I8(bank),
          ..
        })] => DirectiveType::Bank(DbrState::Fixed(*bank)),
        _ => return None,
      },
      ".global" | ".globl" => match &dir.args[..] {
        [Operand::Symbol(sym)] => DirectiveType::Global(*sym),
        _ => return None,
      },
      ".data" | ".fill" | ".skip" | ".space" | ".zero" => {
        let mut args = &dir.args[..];
        if args.is_empty() {
          return None;
        }

        let count = if name == ".data" {
          1
        } else {
          if let Operand::Int(int) = &args[0] {
            args = &args[1..];
            int.value.to_u32() as usize
          } else {
            return None;
          }
        };

        if name == ".zero" && args.len() != 0 {
          return None;
        }

        let mut values = Vec::new();
        for arg in args {
          match arg {
            Operand::Int(int) => values.push(int.value),
            _ => return None,
          }
        }
        DirectiveType::Data { count, values }
      }
      _ => return None,
    };
    Some(dir)
  }
}
