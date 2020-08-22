//! Relocations-related types.

use std::convert::TryInto;

use crate::int::u24;
use crate::int::Int;
use crate::obj::Block;
use crate::syn::operand::Symbol;

/// An error occuring while relocating a symbol.
#[derive(Debug)]
pub enum RelocationError {
  /// Indicates that the symbol's address was not in the expected bank.
  WrongBank {
    /// The bank we wanted.
    expected: u8,
    /// The bank we got.
    got: u8,
  },
  /// Indicates that a symbol was too far; that is, a symbol wasn't actually
  /// within a byte offset range from the `relative_to` field.
  SymbolTooFar,
}

/// A relocation for a missing symbol.
///
/// A `Relocation` describes information that's missing from an assembled
/// `Block`, which can be filled in by a linker.
#[derive(Copy, Clone, Debug)]
pub struct Relocation<'asm> {
  /// Information for resolving the relocation.
  pub info: RelocationInfo,
  /// The symbol that is needed to resolve this relocation.
  pub source: Symbol<'asm>,
}

/// Information describing where a relocation is, and what conditions are
/// necessary to resolve it.
#[derive(Copy, Clone, Debug)]
pub struct RelocationInfo {
  /// An offset into the containing block poing to the exact place where the
  /// symbol value needs to be written.
  pub offset: u16,
  /// The relocation type, which describes how many bytes must be written.
  pub ty: RelocationType,
}

impl RelocationInfo {
  /// Resolves this relocation in the given block, using the given absolute
  /// address as the relocated value.
  pub fn resolve_in(
    self,
    block: &mut Block,
    value: u24,
  ) -> Result<(), RelocationError> {
    let value = match self.ty {
      RelocationType::Absolute => Int::I24(value),
      RelocationType::BankRelative(bank) => {
        if bank == value.bank {
          Int::I16(value.addr)
        } else {
          return Err(RelocationError::WrongBank {
            expected: bank,
            got: value.bank,
          });
        }
      }
      RelocationType::AddrRelative16(address) => {
        if address.bank != value.bank {
          return Err(RelocationError::WrongBank {
            expected: address.bank,
            got: value.bank,
          });
        }

        Int::I16(value.addr.wrapping_sub(address.addr))
      }
      RelocationType::AddrRelative8(address) => {
        if address.bank != value.bank {
          return Err(RelocationError::WrongBank {
            expected: address.bank,
            got: value.bank,
          });
        }

        let offset = value.addr.wrapping_sub(address.addr);
        let offset: i8 = match (offset as i16).try_into() {
          Ok(offset) => offset,
          _ => return Err(RelocationError::SymbolTooFar),
        };
        Int::I8(offset as u8)
      }
    };

    value
      .write_le(&mut block[self.offset..])
      .expect("the space being overwritten should already be zeroed");
    Ok(())
  }
}

/// A type of a relocation.
///
/// A `RelocationType` describes how large the relocation is and what
/// information can be used to compress the symbol's address.
#[derive(Copy, Clone, Debug)]
pub enum RelocationType {
  /// An absolute, 24-bit relocation. No checks necessary.
  Absolute,
  /// A bank-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the given value.
  ///
  /// This type of relocation is useful for most 16-bit addressing modes.
  BankRelative(u8),
  /// An address-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the bank of the given address. In addition, the lower 16 bits of the
  /// address will be subtracted from those of the symbol, forming a relative
  /// offset.
  ///
  /// This type of relocation is useful for 16-bit branches.
  AddrRelative16(u24),
  /// An address-relative 16-bit relocation. The bank byte of the symbol *must*
  /// match the bank of the given address. In addition, the lower 16 bits of the
  /// address will be subtracted from those of the symbol, forming a relative
  /// offset. In addition, this relative offset must be convertible from `i16`
  /// to `i8` without loss of precision.
  ///
  /// This type of relocation is useful for 16-bit branches.
  AddrRelative8(u24),
}
