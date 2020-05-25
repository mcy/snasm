//! Types and functions for manipulating SNES ROM binaries.
//!
//! The SNES uses various methods for mapping a contiguous ROM image onto its
//! address space. The `Rom` trait provides a common interface for accessing a
//! ROM through its mapped addresses.
//!
//! Retro Game Mechanics Explained has a
//! [good video](https://www.youtube.com/watch?v=-U76YvWdnZM) explaining the
//! visual layouts of each mapping mode.

use std::collections::HashMap;

use crate::isa::Long;

/// Mappings for a SNES ROM.
///
/// This essentially provides a fixed virtual memory map: 24-bit SNES virutal
/// addresses are mapped to physical ROM address. Multiple SNES addresses may
/// map to the same ROM address.
///
/// The underlying `Byte` type need not be `u8`; it is sometimes useful to have
/// more complex byte types that include sentinel variants.
pub trait Rom<Byte> {
  /// Returns the number of useable bytes in this ROM.
  fn len(&self) -> usize;

  /// Gets the byte at the SNES address `addr`, if it's been mapped in.
  fn at(&mut self, addr: Long) -> Option<&mut Byte>;
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
/// This `Rom` implementation pretends that WRAM and SRAM do not exist.
pub struct LoRom<Byte> {
  /// Lazily-allocates banks of 256 "bytes" each. This helps keep memory usage
  /// down, since a `Byte` might be bigger than a machine byte, and it's
  /// unlikely we need to map them all in at once.
  ///
  /// The first parameter is the first 24-bit address of each page: `0x222200`
  /// is the `0x22`th page of the bank `0x22`.
  lazy_pages: HashMap<u32, Vec<Byte>>,
  default: Byte,
}

impl<Byte> LoRom<Byte> {
  /// The length of a `LoRom`: four mebibytes.
  pub const LEN: usize = 0x400_000;

  /// Maps `addr` down to a physical address, if such a mapping exists.
  pub fn map(mut addr: Long) -> Option<u32> {
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
}

impl<Byte: Clone> LoRom<Byte> {
  /// Creates a new `LoRom` with the given value of `Byte` in each slot.
  pub fn filled_with(byte: Byte) -> Self {
    Self {
      lazy_pages: HashMap::new(),
      default: byte,
    }
  }

  /// Gets the page containing the given ROM address, triggering an allocation
  /// if necessary.
  fn page_for_rom_addr(&mut self, addr: u32) -> &mut [Byte] {
    let addr = addr & 0xffff00;
    let default = &self.default;
    self.lazy_pages.entry(addr).or_insert_with(|| {
      let mut vec = Vec::with_capacity(0x100);
      for _ in 0..0x100 {
        vec.push(default.clone());
      }
      vec
    })
  }
}

impl<Byte: Clone + Default> LoRom<Byte> {
  /// Creates a new `LoRom` with the default value of `Byte` in each slot.
  pub fn new() -> Self {
    Self::filled_with(Byte::default())
  }
}

impl<Byte: Clone> Rom<Byte> for LoRom<Byte> {
  fn len(&self) -> usize {
    Self::LEN
  }

  fn at(&mut self, addr: Long) -> Option<&mut Byte> {
    Self::map(addr).map(move |a| &mut self.page_for_rom_addr(a)[(a & 0xff) as usize])
  }
}

// TODO(mcyoung): Introduce more mapping modes.

#[cfg(test)]
mod test {
  use super::*;

  macro_rules! assert_mapping {
    ($ty:ident, $val:literal => None) => {
      assert_eq!(
        $ty::<u8>::map(Long::from_u32($val)),
        None
      );
    };
    ($ty:ident, $val:literal => $expected:literal) => {
      assert_eq!(
        $ty::<u8>::map(Long::from_u32($val)),
        Some($expected)
      );
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
