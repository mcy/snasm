//! Types and functions for manipulating SNES ROM binaries.
//!
//! The SNES uses various methods for mapping a contiguous ROM image onto its
//! address space. The [`Rom`] trait provides a common interface for accessing a
//! ROM through its mapped addresses.
//!
//! Retro Game Mechanics Explained has a
//! [good video](https://www.youtube.com/watch?v=-U76YvWdnZM) explaining the
//! visual layouts of each mapping mode.
//!
//! [`Rom`]: trait.Rom.html

use std::io;

use crate::int::u24;

/// Mappings for a SNES ROM.
///
/// This trait abstracts a memory buffer (the "ROM") to an object that can be
/// read and written to through the SNES address space.
pub trait Rom {
  /// Returns the number of useable bytes in this ROM.
  fn len(&self) -> usize;

  /// Gets a reference to the byte at `addr`, if it's been mapped in.
  fn at(&self, addr: u24) -> Option<&u8>;

  /// Gets a mutable reference to the byte at `addr`, if it's been mapped in.
  fn at_mut(&mut self, addr: u24) -> Option<&mut u8>;

  /// Copies a contiguous chunk of this ROM to `data`, starting at `addr`.
  ///
  /// If this function would access to an unmapped address, `Err` is returned
  /// with that address. If `Err` is returned, the read need not have completed
  /// up to that point.
  fn read(&self, addr: u24, data: &mut [u8]) -> Result<(), u24>;

  /// Copies `data` to this ROM, starting at `addr`.
  ///
  /// This function behaves *as if* each byte was copied in sequence.
  ///
  /// If this function would access to an unmapped address, `Err` is returned
  /// with that address. If `Err` is returned, the write need not have completed
  /// up to that point.
  fn write(&mut self, addr: u24, data: &[u8]) -> Result<(), u24>;
}

/// A LoROM-mapped ROM.
///
/// This mapping mode is simple: every half-bank-sized chunk of the ROM mapped
/// to the upper half of each SNES bank, from `0x80` to `0xff`. The top half of
/// this mapping is then mirrored, for banks `0xc0` to `0xff`, to their
/// respective bottom halves. Finally, this upper-half mapping is mirroed to
/// banks `0x00` to `0x7f`, though portions of these may be overriden by SRAM
/// and WRAM.
///
/// The following diagram describes this arrangement (ignoring the bottom half
/// of the SNES address space):
/// ```text
///   $xx0000..$xx7fff   $xx8000..$xxffff
/// +------------------+------------------+
/// |                  | $000000..$007fff | $80xxxx
/// +------------------+------------------+
/// |                  | $008000..$00ffff | $81xxxx
/// +------------------+------------------+
/// |                  | $010000..$017fff | $82xxxx
/// +------------------+------------------+
/// |                  | $018000..$01ffff | $83xxxx
/// +------------------+------------------+
///  ...                                 
/// +------------------+------------------+
/// |                  | $080000..$087fff | $90xxxx
/// +------------------+------------------+
/// |                  | $088000..$08ffff | $91xxxx
/// +------------------+------------------+
///  ...                                 
/// +------------------+------------------+
/// | $200000..$287fff | $200000..$287fff | $c0xxxx
/// +------------------+------------------+
/// | $208000..$28ffff | $208000..$28ffff | $c1xxxx
/// +------------------+------------------+
///  ...                                 
/// +------------------+------------------+
/// | $3e0000..$3e7fff | $3e0000..$3e7fff | $fcxxxx
/// +------------------+------------------+
/// | $3e8000..$3effff | $3e8000..$3effff | $fdxxxx
/// +------------------+------------------+
/// | $3f0000..$3f7fff | $3f0000..$3f7fff | $fexxxx
/// +------------------+------------------+
/// | $3f8000..$3fffff | $3f8000..$3fffff | $ffxxxx
/// +------------------+------------------+
/// ```
/// The empty boxes above are unmapped, or mapped to something else.
///
/// This `Rom` implementation pretends that WRAM and SRAM do not exist.
#[derive(Clone)]
pub struct LoRom {
  bytes: Box<[u8]>,
}

impl LoRom {
  /// The length of a `LoRom`: four mebibytes.
  pub const LEN: usize = 0x40_0000;

  /// Maps `addr` down to a physical address, if such a mapping exists.
  pub fn map(mut addr: u24) -> Option<u32> {
    // For bank bytes with the second highest bit unset, the lower halves are
    // unmapped:
    if addr.bank & 0x40 == 0 && addr.addr & 0x8000 == 0 {
      return None;
    }

    // First note that we do not care about the top bit of the bank byte,
    // due to mirroring; we unset this.
    addr.bank &= !0x80;

    // Further, we also don't care about the top bit of the address, if the
    // second most significant bank byte is set.
    if addr.bank & 0x40 != 0 {
      addr.addr |= 0x8000;
    }

    // For even bank bytes, we want a lower-half of a ROM bank. Thus, we have
    let rom_bank_offset = if addr.bank % 2 == 0 {
      ((addr.bank / 2) as u32) << 16
    }
    // For odd bank bytes, we want an upper-half, instead.
    else {
      (((addr.bank / 2) as u32) << 16) + 0x8000
    };

    Some(rom_bank_offset | ((addr.addr & 0x7fff) as u32))
  }

  /// Computes the largest SNES-address and ROM-address contiguous range
  /// starting at the given address and having at most the given length.
  ///
  /// Returns `None` if `addr` is unmapped.
  fn largest_congituous(addr: u24, len: u32) -> Option<(u32, u32)> {
    // This condition requires only that `addr` be mapped, and continues to the
    // end of the half-bank `addr` is in.
    let rom_addr = Self::map(addr)?;
    let max_len = 0x8000 - (addr.addr & 0x7fff);
    let rom_len = len.min(max_len as u32);
    Some((rom_addr, rom_addr + rom_len))
  }

  /// Creates a new `LoRom` filled with zeroes.
  pub fn new() -> Self {
    Self::filled_with(0)
  }

  /// Creates a new `LoRom` with the given value of `vyte` in each slot.
  pub fn filled_with(byte: u8) -> Self {
    Self {
      bytes: vec![byte; Self::LEN].into_boxed_slice(),
    }
  }

  /// Dumps the (interesting) contents of this ROM to the given `Write`.
  pub fn dump(&self, mut w: impl io::Write) -> io::Result<()> {
    let mut ascii_str = String::new();
    let iter = self
      .bytes
      .chunks(32)
      .enumerate()
      .filter(|(_, c)| c.iter().any(|&byte| byte != 0));
    for (addr, chunk) in iter {
      write!(w, "{:06x}:", addr * 32)?;

      ascii_str.clear();
      for &byte in chunk {
        write!(w, " {:02x}", byte)?;

        if 0x20 <= byte && byte <= 0x7e {
          ascii_str.push(byte as char);
        } else {
          ascii_str.push('.');
        }
      }
      writeln!(w, "  |{}|", ascii_str)?;
    }
    Ok(())
  }

  /// Consumses this `LoRom`, returning the raw ROM bytes.
  pub fn into_bytes(self) -> Box<[u8]> {
    self.bytes
  }
}

impl Rom for LoRom {
  fn len(&self) -> usize {
    Self::LEN
  }

  fn at(&self, addr: u24) -> Option<&u8> {
    Self::map(addr).map(|a| &self.bytes[a as usize])
  }

  fn at_mut(&mut self, addr: u24) -> Option<&mut u8> {
    Self::map(addr).map(move |a| &mut self.bytes[a as usize])
  }

  fn read(&self, mut addr: u24, mut data: &mut [u8]) -> Result<(), u24> {
    while !data.is_empty() {
      let (start, end) = match Self::largest_congituous(addr, data.len() as u32) {
        Some(addrs) => addrs,
        None => return Err(addr),
      };
      let rom_bytes = &self.bytes[start as usize..end as usize];
      let len = rom_bytes.len();
      assert!(len <= u16::MAX as usize);

      data[..len].copy_from_slice(rom_bytes);
      data = &mut data[len..];
      addr = addr.offset_full(len as i16);
    }
    Ok(())
  }

  fn write(&mut self, mut addr: u24, mut data: &[u8]) -> Result<(), u24> {
    while !data.is_empty() {
      let (start, end) = match Self::largest_congituous(addr, data.len() as u32) {
        Some(addrs) => addrs,
        None => return Err(addr),
      };
      let rom_bytes = &mut self.bytes[start as usize..end as usize];
      let len = rom_bytes.len();
      assert!(len <= u16::MAX as usize);

      rom_bytes.copy_from_slice(&data[..len]);
      data = &data[len..];
      addr = addr.offset_full(len as i16);
    }
    Ok(())
  }
}

// TODO(mcyoung): Introduce more mapping modes.

#[cfg(test)]
mod test {
  use super::*;

  macro_rules! assert_mapping {
    ($ty:ident, $val:literal => None) => {
      assert_eq!($ty::map(u24::from_u32($val)), None);
    };
    ($ty:ident, $val:literal => $expected:literal) => {
      assert_eq!($ty::map(u24::from_u32($val)), Some($expected));
    };
  }

  #[test]
  fn lorom_mapping() {
    assert_mapping!(LoRom, 0x00_00_00 => None);
    assert_mapping!(LoRom, 0x00_80_00 => 0x00_00_00);
    assert_mapping!(LoRom, 0x00_ff_ff => 0x00_7f_ff);
    assert_mapping!(LoRom, 0x80_00_00 => None);
    assert_mapping!(LoRom, 0x80_80_00 => 0x00_00_00);
    assert_mapping!(LoRom, 0x80_ff_ff => 0x00_7f_ff);
    assert_mapping!(LoRom, 0x68_00_00 => 0x34_00_00);
    assert_mapping!(LoRom, 0x68_80_00 => 0x34_00_00);
    assert_mapping!(LoRom, 0x68_ff_ff => 0x34_7f_ff);
    assert_mapping!(LoRom, 0xe8_00_00 => 0x34_00_00);
    assert_mapping!(LoRom, 0xe8_80_00 => 0x34_00_00);
    assert_mapping!(LoRom, 0xe8_ff_ff => 0x34_7f_ff);
  }
}
