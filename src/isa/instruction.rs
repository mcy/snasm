//! The 65816 instruction set proper.

use crate::isa::AddrMode;
use crate::isa::Mnemonic;

/// A 65816 instruction.
///
/// An instruction consists of a mnemonic plus an addressing mode, though
/// note all variants are legal. `Instruction::build_from` can be used to
/// construct legal combinations.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instruction {
  mne: Mnemonic,
  mode: AddrMode,
}

impl Instruction {
  /// Gets this instruction's mnemonic.
  pub fn mnemonic(self) -> Mnemonic {
    self.mne
  }

  /// Gets this instruction's addressing mode.
  pub fn addressing_mode(self) -> AddrMode {
    self.mode
  }
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
    $($opcode:literal => $addr_mode:pat),* $(,)?
  })?)*) => {

    impl Instruction {
      /// Attempts to build an instruction from the given mnemonic and
      /// addressing mode.
      ///
      /// If no such instruction is represenatable, `None` is returned.
      pub fn build_from(mne: Mnemonic, mode: AddrMode) -> Option<Instruction> {
        use AddrMode::*;
        match (mne, mode) {
          $($($(
            (Mnemonic::$mne, $addr_mode) => Some(Self { mne, mode }),
          )*)?)*
          $($(
            (Mnemonic::$mne, Inherent) => {
              // Force a macro repetition. repetition.
              let _ = $inh_opcode;
              Some(Self { mne, mode: Inherent })
            }
          )?)*
          _ => None,
        }
      }

      /// Returns this instruction's opcode.
      pub fn opcode(self) -> u8 {
        use AddrMode::*;
        match (self.mnemonic(), self.addressing_mode()) {
          $($($(
            (Mnemonic::$mne, $addr_mode) => $opcode,
          )*)?)*
          $($((Mnemonic::$mne, Inherent) => $inh_opcode,)?)*
          _ => unreachable!(),
        }
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
    0x61 => DirectIndirectX(..),
    0x63 => StackRel(..),
    0x65 => Direct(..),
    0x67 => DirectIndirectLong(..),
    0x69 => Imm(..),
    0x6d => Abs(..),
    0x6f => AbsLong(..),
    0x71 => DirectIndirectY(..),
    0x72 => DirectIndirect(..),
    0x73 => StackRelIndirectY(..),
    0x75 => DirectX(..),
    0x77 => DirectIndirectLongY(..),
    0x79 => AbsY(..),
    0x7d => AbsX(..),
    0x7f => AbsLongX(..),
  }

  Sbc {
    0xe1 => DirectIndirectX(..),
    0xe3 => StackRel(..),
    0xe5 => Direct(..),
    0xe7 => DirectIndirectLong(..),
    0xe9 => Imm(..),
    0xed => Abs(..),
    0xef => AbsLong(..),
    0xf1 => DirectIndirectY(..),
    0xf2 => DirectIndirect(..),
    0xf3 => StackRelIndirectY(..),
    0xf5 => DirectX(..),
    0xf7 => DirectIndirectLongY(..),
    0xf9 => AbsY(..),
    0xfd => AbsX(..),
    0xff => AbsLongX(..),
  }

  And {
    0x21 => DirectIndirectX(..),
    0x23 => StackRel(..),
    0x25 => Direct(..),
    0x27 => DirectIndirectLong(..),
    0x29 => Imm(..),
    0x2d => Abs(..),
    0x2f => AbsLong(..),
    0x31 => DirectIndirectY(..),
    0x32 => DirectIndirect(..),
    0x33 => StackRelIndirectY(..),
    0x35 => DirectX(..),
    0x37 => DirectIndirectLongY(..),
    0x39 => AbsY(..),
    0x3d => AbsX(..),
    0x3f => AbsLongX(..),
  }

  Eor {
    0x41 => DirectIndirectX(..),
    0x43 => StackRel(..),
    0x45 => Direct(..),
    0x47 => DirectIndirectLong(..),
    0x49 => Imm(..),
    0x4d => Abs(..),
    0x4f => AbsLong(..),
    0x51 => DirectIndirectY(..),
    0x52 => DirectIndirect(..),
    0x53 => StackRelIndirectY(..),
    0x55 => DirectX(..),
    0x57 => DirectIndirectLongY(..),
    0x59 => AbsY(..),
    0x5d => AbsX(..),
    0x5f => AbsLongX(..),
  }

  Ora {
    0x01 => DirectIndirectX(..),
    0x03 => StackRel(..),
    0x05 => Direct(..),
    0x07 => DirectIndirectLong(..),
    0x09 => Imm(..),
    0x0d => Abs(..),
    0x0f => AbsLong(..),
    0x11 => DirectIndirectY(..),
    0x12 => DirectIndirect(..),
    0x13 => StackRelIndirectY(..),
    0x15 => DirectX(..),
    0x17 => DirectIndirectLongY(..),
    0x19 => AbsY(..),
    0x1d => AbsX(..),
    0x1f => AbsLongX(..),
  }

  Asl {
    0x06 => Direct(..),
    0x0a => Acc(..),
    0x0e => Abs(..),
    0x16 => DirectX(..),
    0x1e => AbsX(..),
  }

  Lsr {
    0x46 => Direct(..),
    0x4a => Acc(..),
    0x4e => Abs(..),
    0x56 => DirectX(..),
    0x5e => AbsX(..),
  }

  Rol {
    0x26 => Direct(..),
    0x2a => Acc(..),
    0x2e => Abs(..),
    0x36 => DirectX(..),
    0x3e => AbsX(..),
  }

  Ror {
    0x66 => Direct(..),
    0x6a => Acc(..),
    0x6e => Abs(..),
    0x76 => DirectX(..),
    0x7e => AbsX(..),
  }

  Cmp {
    0xc1 => DirectIndirectX(..),
    0xc3 => StackRel(..),
    0xc5 => Direct(..),
    0xc7 => DirectIndirectLong(..),
    0xc9 => Imm(..),
    0xcd => Abs(..),
    0xcf => AbsLong(..),
    0xd1 => DirectIndirectY(..),
    0xd2 => DirectIndirect(..),
    0xd3 => StackRelIndirectY(..),
    0xd5 => DirectX(..),
    0xd7 => DirectIndirectLongY(..),
    0xd9 => AbsY(..),
    0xdd => AbsX(..),
    0xdf => AbsLongX(..),
  }

  Cpx {
    0xe0 => Imm(..),
    0xe4 => Direct(..),
    0xec => Abs(..),
  }

  Cpy {
    0xc0 => Imm(..),
    0xc4 => Direct(..),
    0xcc => Abs(..),
  }

  Dec {
    0x3a => Acc(..),
    0xc6 => Direct(..),
    0xce => Abs(..),
    0xd6 => DirectX(..),
    0xde => AbsX(..),
  }
  Dex = 0xca,
  Dey = 0x88,

  Inc {
    0x1a => Acc(..),
    0xe6 => Direct(..),
    0xee => Abs(..),
    0xf6 => DirectX(..),
    0xfe => AbsX(..),
  }
  Inx = 0xe8,
  Iny = 0xc8,

  Lda {
    0xa1 => DirectIndirectX(..),
    0xa3 => StackRel(..),
    0xa5 => Direct(..),
    0xa7 => DirectIndirectLong(..),
    0xa9 => Imm(..),
    0xad => Abs(..),
    0xaf => AbsLong(..),
    0xb1 => DirectIndirectY(..),
    0xb2 => DirectIndirect(..),
    0xb3 => StackRelIndirectY(..),
    0xb5 => DirectX(..),
    0xb7 => DirectIndirectLongY(..),
    0xb9 => AbsY(..),
    0xbd => AbsX(..),
    0xbf => AbsLongX(..),
  }
  Ldx {
    0xa2 => Imm(..),
    0xa6 => Direct(..),
    0xae => Abs(..),
    0xb6 => DirectY(..),
    0xbe => AbsY(..),
  }
  Ldy {
    0xa0 => Imm(..),
    0xa4 => Direct(..),
    0xac => Abs(..),
    0xb4 => DirectX(..),
    0xbc => AbsX(..),
  }

  Sta {
    0x81 => DirectIndirectX(..),
    0x83 => StackRel(..),
    0x85 => Direct(..),
    0x87 => DirectIndirectLong(..),
    0x8d => Abs(..),
    0x8f => AbsLong(..),
    0x91 => DirectIndirectY(..),
    0x92 => DirectIndirect(..),
    0x93 => StackRelIndirectY(..),
    0x95 => DirectX(..),
    0x97 => DirectIndirectLongY(..),
    0x99 => AbsY(..),
    0x9d => AbsX(..),
    0x9f => AbsLongX(..),
  }
  Stx {
    0x86 => Direct(..),
    0x8e => Abs(..),
    0x96 => DirectY(..),
  }
  Sty {
    0x84 => Direct(..),
    0x8c => Abs(..),
    0x94 => DirectX(..),
  }
  Stz {
    0x64 => Direct(..),
    0x74 => DirectX(..),
    0x9c => Abs(..),
    0x9e => AbsX(..),
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

  Mvn { 0x54 => BlockMove(..) }
  Mvp { 0x44 => BlockMove(..) }

  Pea { 0xf4 => Abs(..) }
  Pei { 0xd4 => Direct(..) }
  Per { 0x62 => PcRel(..) }

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

  Bcc { 0x90 => PcRel(..) }
  Bcs { 0xb0 => PcRel(..) }
  Beq { 0xf0 => PcRel(..) }
  Bne { 0xd0 => PcRel(..) }
  Bmi { 0x30 => PcRel(..) }
  Bpl { 0x10 => PcRel(..) }
  Bvs { 0x50 => PcRel(..) }
  Bvc { 0x70 => PcRel(..) }
  Bra { 0x80 => PcRel(..) }
  Brl { 0x82 => PcRelLong(..) }

  Jmp {
    0x4c => Abs(..),
    0x6c => AbsIndirect(..),
    0x7c => AbsIndirectX(..),
  }
  Jml {
    0x5c => AbsLong(..),
    0xdc => AbsIndirectLong(..),
  }
  Jsr {
    0x20 => Abs(..),
    0xfc => AbsIndirectX(..),
  }
  Jsl { 0x22 => AbsLong(..) }
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

  Rep { 0xc2 => Imm(..) }
  Sep { 0xe2 => Imm(..) }
  Xce = 0xfb,

  Bit {
    0x24 => Direct(..),
    0x2c => Abs(..),
    0x34 => DirectX(..),
    0x3c => AbsX(..),
    0x89 => Imm(..),
  }
  Trb {
    0x14 => Direct(..),
    0x1c => Abs(..),
  }
  Tsb {
    0x04 => Direct(..),
    0x0c => Abs(..),
  }

  Brk = 0x00,
  Cop { 0x02 => Imm(..) }
  Stp = 0xdb,
  Wai = 0xcb,
  Wdm = 0x42,
}
