//! Integer types used by SNASM.
//!
//! SNASM needs to work with a number of different integer types, including
//! the oddball 24-bit 65816 addresses. This module provides types for handling
//! integer values and types cleanly.

use std::fmt;
use std::fmt::Display;
use std::io;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Neg;
use std::ops::Not;

use serde::Deserialize;
use serde::Serialize;

/// A variable-width integer of 8, 16, or 24 bits.
///
/// An `Int` is not meaningfully signed or unsigned; it is merely a collection
/// of bits. The `to_u32()` and `to_i32()` can be used to unify the underlying
/// value via either zero or sign extension.
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
  pub fn best_fit(val: u32) -> Option<Self> {
    Width::smallest_for(val).map(|w| Self::new(val as u32, w))
  }

  /// Zero-extends this `Int` to the given width.
  pub fn zero_extend(self, width: Width) -> Self {
    Self::new(self.to_u32(), width)
  }

  /// Zero-extends this `Int` to the given width.
  ///
  /// Returns `None` if `self` is wider than `width`.
  pub fn zero_extend_checked(self, width: Width) -> Option<Self> {
    if self.width() > width {
      return None;
    }

    Some(self.zero_extend(width))
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

  /// Reads a little-endian `Int` of the given width from a `Read`.
  pub fn read_le(width: Width, mut r: impl io::Read) -> io::Result<Self> {
    match width {
      Width::I8 => {
        let mut buf = [0; 1];
        r.read_exact(&mut buf)?;
        Ok(Int::I8(buf[0]))
      }
      Width::I16 => {
        let mut buf = [0; 2];
        r.read_exact(&mut buf)?;
        Ok(Int::I16(u16::from_le_bytes(buf)))
      }
      Width::I24 => {
        let mut buf = [0; 3];
        r.read_exact(&mut buf)?;
        Ok(Int::I24(u24::from_le_bytes(buf)))
      }
    }
  }

  /// Writes a little-endian `Int` to a `Write`.
  pub fn write_le(&self, mut w: impl io::Write) -> io::Result<()> {
    match self {
      Int::I8(n) => w.write_all(&[*n])?,
      Int::I16(n) => w.write_all(&n.to_le_bytes())?,
      Int::I24(n) => w.write_all(&n.to_le_bytes())?,
    }
    Ok(())
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

impl Neg for Int {
  type Output = Self;
  fn neg(self) -> Self {
    match self {
      Self::I8(n) => Self::I8((n as i8).neg() as u8),
      Self::I16(n) => Self::I16((n as i16).neg() as u16),
      Self::I24(n) => Self::I24(-n),
    }
  }
}

impl Not for Int {
  type Output = Self;
  fn not(self) -> Self {
    match self {
      Self::I8(n) => Self::I8(!n),
      Self::I16(n) => Self::I16(!n),
      Self::I24(n) => Self::I24(!n),
    }
  }
}

/// A 24-bit 64816 address.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[derive(Deserialize, Serialize)]
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

  /// Creates a new `u24` from the given bytes, in little-endian order.
  #[inline]
  pub fn from_le_bytes(bytes: [u8; 3]) -> Self {
    Self {
      bank: bytes[2],
      addr: bytes[0] as u16 | ((bytes[1] as u16) << 8),
    }
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

impl Neg for u24 {
  type Output = Self;
  fn neg(self) -> Self {
    let val = -self.to_i32();
    Self::from_u32(val as u32)
  }
}

impl Not for u24 {
  type Output = Self;
  fn not(self) -> Self {
    Self {
      bank: !self.bank,
      addr: !self.addr,
    }
  }
}

impl Add<u16> for u24 {
  type Output = Self;
  fn add(mut self, addr: u16) -> Self {
    self += addr;
    self
  }
}

impl AddAssign<u16> for u24 {
  fn add_assign(&mut self, addr: u16) {
    self.addr += addr;
  }
}

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

  /// Returns the number of bytes a value of this width contains.
  ///
  /// ```
  /// # use snasm::int::Width;
  /// assert_eq!(Width::I8.bytes(), 1);
  /// ```
  #[inline]
  pub fn bytes(self) -> u32 {
    match self {
      Self::I8 => 1,
      Self::I16 => 2,
      Self::I24 => 3,
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

  /// Checks that the usigned integer `val` can fit into this `Width`.
  ///
  /// ```
  /// # use snasm::int::Width;
  /// assert!(Width::I8.in_range(0));
  /// assert!(Width::I8.in_range(128));
  /// assert!(Width::I8.in_range(255));
  /// assert!(!Width::I8.in_range(256));
  /// ```
  pub fn in_range(self, val: u32) -> bool {
    val & !self.mask() == 0
  }

  /// Returns the smallest `Width` that fits `val`, if such exists.
  /// ```
  /// # use std::i32;
  /// # use snasm::int::Width;
  /// assert_eq!(Width::smallest_for(0), Some(Width::I8));
  /// assert_eq!(Width::smallest_for(255), Some(Width::I8);
  /// assert_eq!(Width::smallest_for(256), Some(Width::I16));
  /// assert_eq!(Width::smallest_for(i32::MAX), None);
  /// ```
  pub fn smallest_for(val: u32) -> Option<Self> {
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
