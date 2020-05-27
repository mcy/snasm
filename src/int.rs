//! Integer types used by SNASM.
//!
//! SNASM needs to work with a number of different integer types, including
//! the oddball 24-bit 65816 addresses. This module provides types for handling
//! integer values and types cleanly.

use std::fmt;
use std::fmt::Display;

/// A variable-width integer of 8, 16, or 24 bits.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum Int {
  /// An 8-bit address.
  I8(u8),
  /// An 16-bit address.
  I16(u16),
  /// An 24-bit address.
  I24(u24),
}

impl Int {
  /// Creates a new `Int` with the given bits and the given width inside it.
  ///
  /// This function will truncate any extraneous bits in `val`.
  #[inline]
  pub fn new(val: u32, width: Width) -> Self {
    match width {
      Width::I8 => Self::I8(val as u8),
      Width::I16 => Self::I16(val as u16),
      Width::I24 => Self::I24(u24::from_u32(val)),
    }
  }

  /// Tries to create a new `Int` with the smallest possible width.
  ///
  /// This function uses `Width::smallest_for()` to find the smallest width that
  /// fits all of the significant bits in `val`.
  #[inline]
  pub fn best_fit(val: i32) -> Option<Self> {
    Width::smallest_for(val).map(|w| Self::new(val as u32, w))
  }

  /// Gets the width of this `Int`.
  #[inline]
  pub fn width(self) -> Width {
    match self {
      Self::I8(_) => Width::I8,
      Self::I16(_) => Width::I16,
      Self::I24(_) => Width::I24,
    }
  }

  /// Zero-extends the value in this `Int` to a `u32`.
  #[inline]
  pub fn to_u32(self) -> u32 {
    match self {
      Self::I8(n) => n as u32,
      Self::I16(n) => n as u32,
      Self::I24(n) => n.to_u32(),
    }
  }

  /// Sign-extends the value in this `Int` to a `i32`.
  #[inline]
  pub fn to_i32(self) -> i32 {
    match self {
      Self::I8(n) => n as i8 as i32,
      Self::I16(n) => n as i16 as i32,
      Self::I24(n) => n.to_i32(),
    }
  }

  /// Returns an iterator over this `Int`'s bytes, in little-endian order.
  pub fn le_bytes(self) -> impl Iterator<Item = u8> {
    struct Iter(Int, usize);
    impl Iterator for Iter {
      type Item = u8;
      fn next(&mut self) -> Option<u8> {
        let val = match self.0 {
          Int::I8(n) => [n].get(self.1).cloned(),
          Int::I16(n) => n.to_le_bytes().get(self.1).cloned(),
          Int::I24(n) => n.to_le_bytes().get(self.1).cloned(),
        };
        if val.is_some() {
          self.1 += 1;
        }
        val
      }
    }
    Iter(self, 0)
  }
}

impl From<u8> for Int {
  #[inline]
  fn from(n: u8) -> Self {
    Int::I8(n)
  }
}

impl From<u16> for Int {
  #[inline]
  fn from(n: u16) -> Self {
    Int::I16(n)
  }
}

impl From<u24> for Int {
  #[inline]
  fn from(n: u24) -> Self {
    Int::I24(n)
  }
}

macro_rules! impl_fmt_int {
  ($($trait:ident),*) => {
    $(impl fmt::$trait for Int {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::$trait::fmt(&self.to_u32(), f)
      }
    })*
  }
}
impl_fmt_int!(Display, Binary, Octal, LowerHex, UpperHex);

/// A 24-bit 64816 address.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct u24 {
  /// The "bank byte", that is, the top byte of the address determining which
  /// bank it corresponds to.
  pub bank: u8,
  /// A 16-bit address within a bank.
  pub addr: u16,
}

impl u24 {
  /// Creates a `u24` by truncating a `u32`.
  #[inline]
  pub const fn from_u32(i: u32) -> Self {
    Self {
      bank: (i >> 16) as u8,
      addr: i as u16,
    }
  }

  /// Zero-extends this `u24` into a `u32`.
  #[inline]
  pub const fn to_u32(self) -> u32 {
    ((self.bank as u32) << 16) | (self.addr as u32)
  }

  /// Sign-extends this `u24` into a `u32`.
  #[inline]
  pub const fn to_i32(self) -> i32 {
    // NOTE: the `as i8 as i32` triggers sign extension. In particular, casting
    // any signed type to any wider type (regardless of signedness) triggers
    // sign extension.
    ((self.bank as i8 as i32) << 16) | (self.addr as i32)
  }

  /// Offsets this `u24`. This does not perform 24-bit arithmetic. Instead,
  /// only the `addr` part is affected, always wrapping around on overflow.
  #[must_use]
  #[inline]
  pub fn offset(self, offset: i16) -> Self {
    let mut copy = self;
    copy.addr = self.addr.wrapping_add(offset as u16);
    copy
  }

  /// Like `offset`, but only returns a value if the computation would not
  /// overflow into the next bank.
  #[must_use]
  #[inline]
  pub fn offset_checked(self, offset: i16) -> Option<Self> {
    self.addr.checked_add(offset as u16).map(|addr| u24 {
      bank: self.bank,
      addr,
    })
  }

  /// Like `offset`, but actually performs a carry to the bank byte.
  #[must_use]
  #[inline]
  pub fn offset_full(self, offset: i16) -> Self {
    u24::from_u32(self.to_u32().wrapping_add(offset as u32))
  }

  /// Converts this `u24`'s bytes into an array, in little-endian order.
  #[inline]
  pub fn to_le_bytes(self) -> [u8; 3] {
    [
      self.addr.to_le_bytes()[0],
      self.addr.to_le_bytes()[1],
      self.bank,
    ]
  }
}

macro_rules! impl_fmt_u24 {
  ($($trait:ident),*) => {
    $(impl fmt::$trait for u24 {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::$trait::fmt(&self.to_u32(), f)
      }
    })*
  }
}
impl_fmt_u24!(Display, Binary, Octal, LowerHex, UpperHex);

/// An integer Width: a one, two, or three-byte integers.
///
/// This enum is ordered: smaller integer types compare smaller than bigger
/// integer types.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Width {
  /// A single byte.
  I8,
  /// A two-byte word.
  I16,
  /// A three-byte long.
  I24,
}

impl Width {
  /// Parses a string into an `Width`.
  ///
  /// Valid names are `i8`, `i16` and `i24`, case-insensitive.
  ///
  /// ```
  /// # use snasm::int::Width;
  /// assert_eq!(Width::from_name("i8"), Width::I8);
  /// ```
  #[inline]
  pub fn from_name(s: &str) -> Option<Self> {
    match s {
      "i8" | "I8" => Some(Self::I8),
      "i16" | "I16" => Some(Self::I16),
      "i24" | "I24" => Some(Self::I24),
      _ => None,
    }
  }

  /// Returns a name for this type.
  ///
  /// ```
  /// # use snasm::int;
  /// assert_eq!(Width::I8.name(), "i8");
  /// ```
  #[inline]
  pub fn name(self) -> &'static str {
    match self {
      Self::I8 => "i8",
      Self::I16 => "i16",
      Self::I24 => "i24",
    }
  }

  /// Returns the number of bits a value of this width contains.
  ///
  /// ```
  /// # use snasm::int::Width;
  /// assert_eq!(Width::I8.bits(), 8);
  /// ```
  #[inline]
  pub fn bits(self) -> u32 {
    match self {
      Self::I8 => 8,
      Self::I16 => 16,
      Self::I24 => 24,
    }
  }

  /// Returns the mask for this type.
  ///
  /// A type's mask can be used to extract the bottom `bits()` bits from an
  /// integer.
  #[inline]
  pub fn mask(self) -> u32 {
    match self {
      Self::I8 => 0xff,
      Self::I16 => 0xffff,
      Self::I24 => 0xffffff,
    }
  }

  /// Checks that the integer `val` can fit into this `Width`.
  ///
  /// To "fit in", it either needs to be in-range as a signed integer, or as
  /// an unsigned integer. This boils down to "are the unused bits all ones,
  /// or all zeroes?".
  ///
  /// `val` is accepted as a signed integer, since the sign of `val` affects
  /// whether it fits ro not.
  /// ```
  /// # use snasm::int::Width;
  /// assert!(Width::I8.in_range(0));
  /// assert!(Width::I8.in_range(128));
  /// assert!(Width::I8.in_range(255));
  /// assert!(!Width::I8.in_range(256));
  /// assert!(Width::I8.in_range(-128));
  /// assert!(!Width::I8.in_range(-129));
  /// ```
  pub fn in_range(self, val: i32) -> bool {
    let val = val as u32;

    // The criterion is as follows: either:
    // - All "insignificant" bits are zero, that is, the number is positive
    //   and in-range,
    // - All "insignificant" bits are one, and the highest "significant" bit is
    //   set (i.e., the number would be negative).
    let insignificant = !self.mask();
    let sign_bit = val & (self.mask() + 1 >> 1) != 0;

    val & insignificant == 0
      || (val & insignificant == insignificant && sign_bit)
  }

  /// Returns the smallest unsigned `Width` that fits `val`, if such exists.
  ///
  /// Positive numbers are treated as unsigned; negative numbers, however, are
  /// reated as signed, and so will require an extra bit for the sign bit.
  /// Negative numbers are simply treated as alternate representations for
  /// positive, unsigned numbers. When in doubt, stick add an explicit prefix.
  ///
  /// ```
  /// # use std::i32;
  /// # use snasm::int::Width;
  /// assert_eq!(Width::smallest_for(0), Some(Width::I8));
  /// assert_eq!(Width::smallest_for(255), Some(Width::I8);
  /// assert_eq!(Width::smallest_for(256), Some(Width::I16));
  /// assert_eq!(Width::smallest_for(-128), Some(Width::I8));
  /// assert_eq!(Width::smallest_for(-129), Some(Width::I16));
  /// assert_eq!(Width::smallest_for(i32::MAX), None);
  /// ```
  pub fn smallest_for(val: i32) -> Option<Self> {
    [Self::I8, Self::I16, Self::I24]
      .iter()
      .copied()
      .find(|i| i.in_range(val))
  }
}

impl Display for Width {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}", self.name())
  }
}
