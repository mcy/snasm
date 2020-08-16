//! The 65816 instruction set proper.

use std::io;

use crate::int::Width;
use crate::int::Int;
use crate::isa::Mnemonic;
use crate::syn::AddrExpr;

/// A 65816 instruction.
///
/// An instruction consists of a mnemonic plus an addressing mode, though
/// note all variants are legal. `Instruction::build_from` can be used to
/// construct legal combinations.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instruction {
  mne: Mnemonic,
  mode: Option<AddrExpr<Int>>,
  opcode: u8,
}

impl Instruction {
  /// Gets this instruction's mnemonic.
  pub fn mnemonic(&self) -> Mnemonic {
    self.mne
  }

  /// Gets this instruction's addressing mode.
  pub fn addressing_mode(&self) -> Option<AddrExpr<Int>> {
    self.mode
  }

  /// Gets this instruction's unique opcode.
  pub fn opcode(&self) -> u8 {
    self.opcode
  }
}

macro_rules! addr_helper {
  ($expr:tt, $expr2:tt => $variant:ident($int:ident(_), $int2:ident(_) $($rest:tt)*)) => {
    AddrExpr::$variant($int($expr), $int2($expr2) $($rest)*)
  };
  ($expr:tt, $expr2:tt => $variant:ident($int:ident(_) $($rest:tt)*)) => {
    AddrExpr::$variant($int($expr) $($rest)*)
  };
  ($expr:tt, $expr2:tt => $variant:ident) => {
    AddrExpr::$variant
  };
}

macro_rules! addr_helper_read {
  ($r:expr => $variant:ident($int:ident(_), $int2:ident(_) $($rest:tt)*)) => {{
    let mut r = $r;
    let int = Int::read_le(Width::$int, &mut r)?;
    let int2 = Int::read_le(Width::$int2, &mut r)?;
    // Note the reversed order.
    AddrExpr::$variant(int2, int $($rest)*)
  }};
  ($r:expr => $variant:ident($int:ident(_) $($rest:tt)*)) => {{
    let int = Int::read_le(Width::$int, $r)?;
    AddrExpr::$variant(int $($rest)*)
  }};
  ($r:expr => $variant:ident) => {
    AddrExpr::$variant
  };
}

macro_rules! addr_helper_write {
  ($w:expr, $mode:expr => $variant:ident($int:ident(_), $int2:ident(_) $($rest:tt)*)) => {
    if let Some(AddrExpr::$variant(a @ $int(_), b @ $int2(_) $($rest)*)) = $mode {
      a.write_le(&mut $w)?;
      b.write_le(&mut $w)?;
    }
  };
  ($w:expr, $mode:expr => $variant:ident($int:ident(_) $($rest:tt)*)) => {
    if let Some(AddrExpr::$variant(a @ $int(_) $($rest)*)) = $mode {
      a.write_le(&mut $w)?;
    }
  };
  ($w:expr, $mode:expr => $variant:ident) => {{}};
}

macro_rules! addr_helper_count {
  ($variant:ident($int:ident(_), $int2:ident(_) $($rest:tt)*)) => {
    Width::$int.bytes() + Width::$int2.bytes()
  };
  ($variant:ident($int:ident(_) $($rest:tt)*)) => {
    Width::$int.bytes()
  };
  ($variant:ident) => { 0 };
}

/// A macro for generating `Instruction` rules, i.e., which combinations of
/// mnemonic + addr mode are allowed, and what opcode that maps to.
///
/// # Syntax
/// ```ignore
/// instructions! {
///   /// Multiple instruction mnemonic
///   Abc {
///     0xopcode => AddrMode,
///     // ...
///   }
///   
///   /// No-argument mnemonic
///   Xyz = 0xopcode,
/// }
/// ```
macro_rules! instructions {
  ($($mne:ident $(= $inh_opcode:literal,)? $({
    $($opcode:literal => $addr_mode:ident$(($($addr_args:tt)*))?),* $(,)?
  })?)*) => {

    impl Instruction {
      /// Attempts to build an instruction from the given mnemonic and
      /// addressing mode.
      ///
      /// If no such instruction is represenatable, `None` is returned.
      pub fn build_from(mne: Mnemonic, mode: Option<AddrExpr<Int>>) -> Option<Instruction> {
        use crate::syn::IdxReg::*;
        use crate::int::Int::*;
        match (mne, mode) {
          $($($(
            (Mnemonic::$mne, mode @
              Some(addr_helper!(_, _ => $addr_mode$(($($addr_args)*))?))) =>
              Some(Self { mne, mode, opcode: $opcode }),
          )*)?)*
          $($(
            (Mnemonic::$mne, None) => {
              Some(Self { mne, mode: None, opcode: $inh_opcode })
            }
          )?)*
          _ => None,
        }
      }

      /// Attempts to parse an instruction from the given `Read`.
      pub fn read(mut r: impl io::Read) -> io::Result<Instruction> {
        use crate::syn::IdxReg::*;
        
        let mut opcode = [0u8];
        r.read_exact(&mut opcode)?;
        let opcode = opcode[0];
        match opcode {
          $($($(
            $opcode => {
              let mne = Mnemonic::$mne;
              let mode = addr_helper_read!(r =>
                  $addr_mode$(($($addr_args)*))?);
              Ok(Self { mne, mode: Some(mode), opcode })
            }
          )*)?)*
          $($(
            $inh_opcode => {
              let mne = Mnemonic::$mne;
              Ok(Self { mne, mode: None, opcode: $inh_opcode })
            }
          )?)*
        }
      }

      /// Attempts to write this instruction to the given `Write`
      pub fn write(&self, mut w: impl io::Write) -> io::Result<()> {
        use crate::syn::IdxReg::*;
        use crate::int::Int::*;        
        w.write_all(&[self.opcode])?;
        match self.opcode {
          $($($(
            $opcode => {
              addr_helper_write!(w, self.mode =>
                  $addr_mode$(($($addr_args)*))?);
              Ok(())
            }
          )*)?)*
          $($(
            $inh_opcode => Ok(()),
          )?)*
        }
      }

      /// Computes how many bytes are needed to encode this instruction.
      #[inline]
      pub fn encoded_len(&self) -> usize {
        Self::encoded_len_for_opcode(self.opcode())
      }

      /// Computes how many bytes are needed to encode an instruction starting
      /// with the given opcode.
      pub fn encoded_len_for_opcode(opcode: u8) -> usize {
        (1 + match opcode {
          $($($(
            $opcode => addr_helper_count!($addr_mode$(($($addr_args)*))?),
          )*)?)*
          $($(
            $inh_opcode => 0,
          )?)*
        }) as usize
      } 
    }

    #[test]
    fn unique_opcodes() {
      let declared_opcodes = &[
        $($($($opcode,)*)?)*
        $($($inh_opcode,)?)*
      ][..];

      let mut set = std::collections::HashSet::new();
      for op in declared_opcodes {
        assert!(!set.contains(op), "duplicate opcode: {:#x}", op);
        set.insert(*op);
      }

      for op in 0x00..=0xff {
        assert!(set.contains(&op), "missing opcode: {:#x}", op);
      }
    }
  }
}

instructions! {
  Nop = 0xea,

  Adc {
    0x61 => IdxInd(I8(_), X),
    0x63 => Idx(I8(_), S),
    0x65 => Abs(I8(_)),
    0x67 => LongInd(I8(_)),
    0x69 => Imm(I16(_)),
    0x6d => Abs(I16(_)),
    0x6f => Abs(I24(_)),
    0x71 => IndIdx(I8(_), Y),
    0x72 => Ind(I8(_)),
    0x73 => IdxIndIdx(I8(_), S, Y),
    0x75 => Idx(I8(_), X),
    0x77 => LongIndIdx(I24(_), Y),
    0x79 => Idx(I16(_), Y),
    0x7d => Idx(I16(_), X),
    0x7f => Idx(I24(_), X),
  }

  Sbc {
    0xe1 => IdxInd(I8(_), X),
    0xe3 => Idx(I8(_), S),
    0xe5 => Abs(I8(_)),
    0xe7 => LongInd(I8(_)),
    0xe9 => Imm(I16(_)),
    0xed => Abs(I16(_)),
    0xef => Abs(I24(_)),
    0xf1 => IndIdx(I8(_), Y),
    0xf2 => Ind(I8(_)),
    0xf3 => IdxIndIdx(I8(_), S, Y),
    0xf5 => Idx(I8(_), X),
    0xf7 => LongIndIdx(I24(_), Y),
    0xf9 => Idx(I16(_), Y),
    0xfd => Idx(I16(_), X),
    0xff => Idx(I24(_), X),
  }

  And {
    0x21 => IdxInd(I8(_), X),
    0x23 => Idx(I8(_), S),
    0x25 => Abs(I8(_)),
    0x27 => LongInd(I8(_)),
    0x29 => Imm(I16(_)),
    0x2d => Abs(I16(_)),
    0x2f => Abs(I24(_)),
    0x31 => IndIdx(I8(_), Y),
    0x32 => Ind(I8(_)),
    0x33 => IdxIndIdx(I8(_), S, Y),
    0x35 => Idx(I8(_), X),
    0x37 => LongIndIdx(I24(_), Y),
    0x39 => Idx(I16(_), Y),
    0x3d => Idx(I16(_), X),
    0x3f => Idx(I24(_), X),
  }

  Eor {
    0x41 => IdxInd(I8(_), X),
    0x43 => Idx(I8(_), S),
    0x45 => Abs(I8(_)),
    0x47 => LongInd(I8(_)),
    0x49 => Imm(I16(_)),
    0x4d => Abs(I16(_)),
    0x4f => Abs(I24(_)),
    0x51 => IndIdx(I8(_), Y),
    0x52 => Ind(I8(_)),
    0x53 => IdxIndIdx(I8(_), S, Y),
    0x55 => Idx(I8(_), X),
    0x57 => LongIndIdx(I24(_), Y),
    0x59 => Idx(I16(_), Y),
    0x5d => Idx(I16(_), X),
    0x5f => Idx(I24(_), X),
  }

  Ora {
    0x01 => IdxInd(I8(_), X),
    0x03 => Idx(I8(_), S),
    0x05 => Abs(I8(_)),
    0x07 => LongInd(I8(_)),
    0x09 => Imm(I16(_)),
    0x0d => Abs(I16(_)),
    0x0f => Abs(I24(_)),
    0x11 => IndIdx(I8(_), Y),
    0x12 => Ind(I8(_)),
    0x13 => IdxIndIdx(I8(_), S, Y),
    0x15 => Idx(I8(_), X),
    0x17 => LongIndIdx(I24(_), Y),
    0x19 => Idx(I16(_), Y),
    0x1d => Idx(I16(_), X),
    0x1f => Idx(I24(_), X),
  }

  Asl {
    0x06 => Abs(I8(_)),
    0x0a => Acc,
    0x0e => Abs(I16(_)),
    0x16 => Idx(I8(_), X),
    0x1e => Idx(I16(_), X),
  }

  Lsr {
    0x46 => Abs(I8(_)),
    0x4a => Acc,
    0x4e => Abs(I16(_)),
    0x56 => Idx(I8(_), X),
    0x5e => Idx(I16(_), X),
  }

  Rol {
    0x26 => Abs(I8(_)),
    0x2a => Acc,
    0x2e => Abs(I16(_)),
    0x36 => Idx(I8(_), X),
    0x3e => Idx(I16(_), X),
  }

  Ror {
    0x66 => Abs(I8(_)),
    0x6a => Acc,
    0x6e => Abs(I16(_)),
    0x76 => Idx(I8(_), X),
    0x7e => Idx(I16(_), X),
  }

  Cmp {
    0xc1 => IdxInd(I8(_), X),
    0xc3 => Idx(I8(_), S),
    0xc5 => Abs(I8(_)),
    0xc7 => LongInd(I8(_)),
    0xc9 => Imm(I16(_)),
    0xcd => Abs(I16(_)),
    0xcf => Abs(I24(_)),
    0xd1 => IndIdx(I8(_), Y),
    0xd2 => Ind(I8(_)),
    0xd3 => IdxIndIdx(I8(_), S, Y),
    0xd5 => Idx(I8(_), X),
    0xd7 => LongIndIdx(I24(_), Y),
    0xd9 => Idx(I16(_), Y),
    0xdd => Idx(I16(_), X),
    0xdf => Idx(I24(_), X),
  }

  Cpx {
    0xe0 => Imm(I16(_)),
    0xe4 => Abs(I8(_)),
    0xec => Abs(I16(_)),
  }

  Cpy {
    0xc0 => Imm(I16(_)),
    0xc4 => Abs(I8(_)),
    0xcc => Abs(I16(_)),
  }

  Dec {
    0x3a => Acc,
    0xc6 => Abs(I8(_)),
    0xce => Abs(I16(_)),
    0xd6 => Idx(I8(_), X),
    0xde => Idx(I16(_), X),
  }
  Dex = 0xca,
  Dey = 0x88,

  Inc {
    0x1a => Acc,
    0xe6 => Abs(I8(_)),
    0xee => Abs(I16(_)),
    0xf6 => Idx(I8(_), X),
    0xfe => Idx(I16(_), X),
  }
  Inx = 0xe8,
  Iny = 0xc8,

  Lda {
    0xa1 => IdxInd(I8(_), X),
    0xa3 => Idx(I8(_), S),
    0xa5 => Abs(I8(_)),
    0xa7 => LongInd(I8(_)),
    0xa9 => Imm(I16(_)),
    0xad => Abs(I16(_)),
    0xaf => Abs(I24(_)),
    0xb1 => IndIdx(I8(_), Y),
    0xb2 => Ind(I8(_)),
    0xb3 => IdxIndIdx(I8(_), S, Y),
    0xb5 => Idx(I8(_), X),
    0xb7 => LongIndIdx(I24(_), Y),
    0xb9 => Idx(I16(_), Y),
    0xbd => Idx(I16(_), X),
    0xbf => Idx(I24(_), X),
  }
  Ldx {
    0xa2 => Imm(I16(_)),
    0xa6 => Abs(I8(_)),
    0xae => Abs(I16(_)),
    0xb6 => Idx(I8(_), Y),
    0xbe => Idx(I16(_), Y),
  }
  Ldy {
    0xa0 => Imm(I16(_)),
    0xa4 => Abs(I8(_)),
    0xac => Abs(I16(_)),
    0xb4 => Idx(I8(_), X),
    0xbc => Idx(I16(_), X),
  }

  Sta {
    0x81 => IdxInd(I8(_), X),
    0x83 => Idx(I8(_), S),
    0x85 => Abs(I8(_)),
    0x87 => LongInd(I8(_)),
    0x8d => Abs(I16(_)),
    0x8f => Abs(I24(_)),
    0x91 => IndIdx(I8(_), Y),
    0x92 => Ind(I8(_)),
    0x93 => IdxIndIdx(I8(_), S, Y),
    0x95 => Idx(I8(_), X),
    0x97 => LongIndIdx(I24(_), Y),
    0x99 => Idx(I16(_), Y),
    0x9d => Idx(I16(_), X),
    0x9f => Idx(I24(_), X),
  }
  Stx {
    0x86 => Abs(I8(_)),
    0x8e => Abs(I16(_)),
    0x96 => Idx(I8(_), Y),
  }
  Sty {
    0x84 => Abs(I8(_)),
    0x8c => Abs(I16(_)),
    0x94 => Idx(I8(_), X),
  }
  Stz {
    0x64 => Abs(I8(_)),
    0x74 => Idx(I8(_), X),
    0x9c => Abs(I16(_)),
    0x9e => Idx(I16(_), X),
  }

  Tax = 0xaa,
  Txa = 0x8a,
  Tay = 0xa8,
  Tya = 0x98,
  Tcd = 0x5b,
  Tdc = 0x7b,
  Tcs = 0x1b,
  Tsc = 0x3b,
  Tsx = 0xba,
  Txs = 0x9a,
  Txy = 0x9b,
  Tyx = 0xbb,
  Xba = 0xeb,

  Mvn { 0x54 => Move(I8(_), I8(_)) }
  Mvp { 0x44 => Move(I8(_), I8(_)) }

  Pea { 0xf4 => Abs(I16(_)) }
  Pei { 0xd4 => Abs(I8(_)) }
  Per { 0x62 => Abs(I8(_)) }

  Pha = 0x48,
  Phb = 0x8b,
  Phd = 0x0b,
  Phk = 0x4b,
  Php = 0x08,
  Phx = 0xda,
  Phy = 0x5a,

  Pla = 0x68,
  Plb = 0xab,
  Pld = 0x2b,
  Plp = 0x28,
  Plx = 0xfa,
  Ply = 0x7a,

  Bcc { 0x90 => Abs(I8(_)) }
  Bcs { 0xb0 => Abs(I8(_)) }
  Beq { 0xf0 => Abs(I8(_)) }
  Bne { 0xd0 => Abs(I8(_)) }
  Bmi { 0x30 => Abs(I8(_)) }
  Bpl { 0x10 => Abs(I8(_)) }
  Bvs { 0x50 => Abs(I8(_)) }
  Bvc { 0x70 => Abs(I8(_)) }
  Bra { 0x80 => Abs(I8(_)) }
  Brl { 0x82 => Abs(I16(_)) }

  Jmp {
    0x4c => Abs(I16(_)),
    0x6c => Ind(I16(_)),
    0x7c => IdxInd(I16(_), X),
    0x5c => Abs(I24(_)),
    0xdc => LongInd(I24(_)),
  }
  Jsr {
    0x20 => Abs(I16(_)),
    0xfc => IdxInd(I16(_), X),
    0x22 => Abs(I24(_)),
  }
  Rti = 0x40,
  Rts = 0x60,
  Rtl = 0x6b,

  Clc = 0x18,
  Sec = 0x38,
  Cld = 0xd8,
  Sed = 0xf8,
  Cli = 0x58,
  Sei = 0x78,
  Clv = 0xb8,

  Rep { 0xc2 => Imm(I8(_)) }
  Sep { 0xe2 => Imm(I8(_)) }
  Xce = 0xfb,

  Bit {
    0x24 => Abs(I8(_)),
    0x2c => Abs(I16(_)),
    0x34 => Idx(I8(_), X),
    0x3c => Idx(I16(_), X),
    0x89 => Imm(I16(_)),
  }
  Trb {
    0x14 => Abs(I8(_)),
    0x1c => Abs(I16(_)),
  }
  Tsb {
    0x04 => Abs(I8(_)),
    0x0c => Abs(I16(_)),
  }

  Brk = 0x00,
  Cop { 0x02 => Imm(I8(_)) }
  Stp = 0xdb,
  Wai = 0xcb,
  Wdm = 0x42,
}
