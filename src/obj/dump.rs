//! Objdump implementation for SNASM objects.

use std::io;

use crate::isa::Instruction;
use crate::obj::dbg::OffsetType;
use crate::obj::relo::RelocationType;
use crate::obj::Object;
use crate::syn::fmt;

/// Dumps this object in the style of `objdump` to `w`.
pub fn dump(obj: &Object, mut w: impl io::Write) -> io::Result<()> {
  for (name, addr) in obj.globals() {
    writeln!(w, ".global {}, 0x{:06x}", name, addr)?;
  }
  let mut blocks = obj.blocks().collect::<Vec<_>>();
  blocks.sort_by_key(|&(start, _)| start);

  for (addr, block) in blocks {
    if block.len() == 0 {
      continue;
    }
    writeln!(w, ".origin 0x{:06x}", addr)?;
    for offset in block.offsets() {
      let start = offset.start;
      let end = start + offset.len;

      match offset.ty {
        OffsetType::Code => {
          let mut addr = addr.to_u32() + start as u32;
          for instruction in Instruction::stream(&block[start..end]) {
            let instruction = instruction?;

            write!(w, "{:06x}:", addr)?;
            for byte in instruction.bytes() {
              write!(w, "  {:02x}", byte)?;
            }

            let expected_len = instruction.encoded_len() * 4;
            let padding = 16 - expected_len;
            for _ in 0..padding {
              write!(w, " ")?;
            }

            addr += instruction.encoded_len() as u32;
            fmt::print_instruction(
              fmt::Options::default(),
              instruction,
              &mut w,
            )?;
            writeln!(w, "")?;
          }
        }
        OffsetType::Data => {
          for (n, j) in (start..end).into_iter().enumerate() {
            if n % 8 == 0 {
              if n != 0 {
                writeln!(w, "")?;
              }
              write!(w, "{:06x}:", addr.to_u32() + start as u32 + n as u32)?;
            }
            write!(w, "  {:02x}", block[j])?;
          }
          writeln!(w, "")?;
        }
      }
    }

    for relocation in block.relocations() {
      match relocation.info.ty {
        RelocationType::Absolute => writeln!(
          w,
          ".reloc.i24 0x{:04x} {}",
          relocation.info.offset, relocation.source
        )?,
        RelocationType::BankRelative(bank) => writeln!(
          w,
          ".reloc.i16 0x{:04x} {}@{:02x}",
          relocation.info.offset, relocation.source, bank
        )?,
        RelocationType::AddrRelative16(addr) => writeln!(
          w,
          ".reloc.i16 0x{:04x} {}@{:02x}:{:04x}",
          relocation.info.offset, relocation.source, addr.bank, addr.addr
        )?,
        RelocationType::AddrRelative8(addr) => writeln!(
          w,
          ".reloc.i8 0x{:04x} {}@{:02x}:{:04x}",
          relocation.info.offset, relocation.source, addr.bank, addr.addr
        )?,
      }
    }
  }

  Ok(())
}
