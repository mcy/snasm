//! 65816 addressing modes with operands.
//!
//! Each struct describes the necessary immediate values for each addressing
//! mode, and how machine state is used to compute an effective address from
//! them, in both prose and pseudocode. The assembler syntax is demonstrated
//! with the unused opcode `xyz`.
//!
//! The various "inherent" addressing modes are not included as standalone
//! structs, but are covered in the [`AddrMode`](enum.AddrMode.html) enum.

use crate::isa::Long;
use crate::syn::SymOr;

/// A 65815 addressing mode.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AddrMode {
  /// Absolute addressing.
  Abs(Abs),
  /// Absolute, `x`-indexed addressing.
  AbsX(AbsX),
  /// Absolute, `y`-indexed addressing.
  AbsY(AbsY),
  /// Absolute indirect addressing.
  AbsIndirect(AbsIndirect),
  /// Absolute, `x`-indexed indirect addressing.
  AbsIndirectX(AbsIndirectX),
  /// Absolute indirect long addressing.
  AbsIndirectLong(AbsIndirectLong),
  /// Absolute long addressing.
  AbsLong(AbsLong),
  /// Absolute, `x`-indexed long addressing.
  AbsLongX(AbsLongX),
  /// Accumulator addressing.
  Acc(Acc),
  /// Block move addressing.
  BlockMove(BlockMove),
  /// Direct addressing.
  Direct(Direct),
  /// Direct `x`-indexed addressing.
  DirectX(DirectX),
  /// Direct `y`-indexed addressing.
  DirectY(DirectY),
  /// Direct indirect addressing.
  DirectIndirect(DirectIndirect),
  /// Direct, `x`-indexed indirect addresing.
  DirectIndirectX(DirectIndirectX),
  /// Direct, `y`-indexed indirect addresing.
  DirectIndirectY(DirectIndirectX),
  /// Direct indirect long addressing.
  DirectIndirectLong(DirectIndirectLong),
  /// Direct `y`-indexed indirect long addressing.
  DirectIndirectLongY(DirectIndirectLongY),
  /// Immediate.
  Imm(Imm),
  /// Inherent addressing.
  ///
  /// This variant encompasses all "interesting" addressing modes, such as
  /// the various stack push/pull modes.
  Inherent,
  /// `pc`-relative addressing.
  PcRel(PcRel),
  /// `pc`-relative long addressing.
  PcRelLong(PcRelLong),
  /// `s`-relative addressing.
  StackRel(StackRel),
  /// `s`-relative, `y`-indexed indirect addressing.
  StackRelIndirectY(StackRelIndirectY),
}

/// Absolute addressing.
///
/// The effective address is the relevant bank register offset by `imm`:
/// ```text
/// let addr = dbr ++ imm;
/// ```
/// # Syntax
/// ```text
/// xyz $1234
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Abs {
  /// The immediate operand.
  pub imm: SymOr<u16>,
}

/// Absolute `x`-indexed addressing.
///
/// The effective address is the DBR offset by `imm`, which is then further
/// offset by `x`.
/// ```text
/// let addr = (dbr ++ imm) + x;
/// ```
/// # Syntax
/// ```text
/// xyz $1245, x
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsX {
  /// The immediate operand.
  imm: SymOr<u16>,
}

/// Absolute `y`-indexed addressing.
///
/// The effective address is the DBR offset by `imm`, which is then further
/// offset by `y`.
/// ```text
/// let addr = (dbr ++ imm) + y;
/// ```
/// # Syntax
/// ```text
/// xyz $1234, y
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsY {
  /// The immediate operand.
  imm: SymOr<u16>,
}

/// Absolute indirect addressing.
///
/// The effective address is computed by looking up a little-endian `u16` in
/// the zero bank; this value is used to offset the PBR.
/// ```text
/// let addr = pbr ++ *imm;
/// ```
/// # Syntax
/// ```text
/// xyz ($1234)
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsIndirect {
  /// The immediate operand.
  imm: SymOr<u16>,
}

/// Absolute, indexed, indirect addressing.
///
/// The effective address is computed by taking the sum of `imm` and `x`,
/// which is used to look up a little-endian `u16` in the current program
/// bank; this is used to once again offset the PBR.
/// ```text
/// let addr = pbr ++ *((pbr ++ imm) + x);
/// ```
/// # Syntax
/// ```text
/// xyz ($1234, x)
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsIndirectX {
  /// The immediate operand.
  imm: SymOr<u16>,
}

/// Absolute, indirect, long addressing.
///
/// The effective address is the `u24` located at `imm`.
/// ```text
/// let addr = *imm;
/// ```
/// # Syntax
/// ```text
/// xyz [$123456]
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsIndirectLong {
  /// The immediate operand.
  imm: SymOr<Long>,
}

/// Absolute long addressing.
///
/// The effective address is simply `imm`.
/// ```text
/// let addr = imm;
/// ```
/// # Syntax
/// ```text
/// xyz $123456
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsLong {
  /// The immediate operand.
  imm: SymOr<Long>,
}

/// Absolute long, `x`-indexed addressing.
///
/// The effective address is `imm` plus `x`.
/// ```text
/// let addr = imm + x;
/// ```
/// # Syntax
/// ```text
/// xyz $123456, x
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsLongX {
  /// The immediate operand.
  imm: SymOr<Long>,
}

/// Accumulator addressing.
///
/// The effective address is the accumulator itself.
/// ```text
/// let addr = &a;
/// ```
/// # Syntax
/// ```text
/// xyz a
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Acc;

/// Block move addressing.
///
/// This addressing mode is used by the `mvn` and `mvp` "`memmove`-like"
/// instructions. As such, the operands are merely bank bytes specifying
/// the source and destination banks for the copy.
///
/// # Syntax
/// ```text
/// xyz $12, $34
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BlockMove {
  /// The bank byte for the source addresses.
  src_bank: SymOr<u8>,
  /// The bank byte the the destination addresses.
  dest_bank: SymOr<u8>,
}

/// Direct page addressing.
///
/// The effective address is the `d` register offset by `imm`, in the zero
/// bank.
/// ```text
/// let addr = d + imm;
/// ```
/// # Syntax
/// ```text
/// xyz $12
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Direct {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct, `x`-indexed addressing.
///
/// The effective address is the `d` register offset by `imm`, which is
/// then indexed by `x`; this address is resolved in the zero bank.
/// ```text
/// let addr = (d + imm) + x;
/// ```
/// # Syntax
/// ```text
/// xyz $12, x
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectX {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct, `y`-indexed addressing.
///
/// The effective address is the `d` register offset by `imm`, which is
/// then indexed by `y`; this address is resolved in the zero bank.
/// ```text
/// let addr = (d + imm) + y;
/// ```
/// # Syntax
/// ```text
/// xyz $12, y
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectY {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct page indicrect addressing.
///
/// To compute the effective address, we add together `d` and `imm`, which is
/// used to look up a `u16` in the zero bank, which is then used to offset
/// the DBR.
/// ```text
/// let addr = dbr ++ *(d + imm);
/// ```
/// # Syntax
/// ```text
/// xyz ($12)
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectIndirect {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct, `x`-indexed indirect addressing.
///
/// To compute the effective address, we first add `d`, `x`, and `imm`.
/// This is then used to look up a `u16` in the zero bank, which is used to
/// offset the DBR.
/// ```text
/// let addr = dbr ++ *(d + imm + x);
/// ```
/// # Syntax
/// ```text
/// xyz ($12, x)
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectIndirectX {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct `y`-indexed indirect addressing.
///
/// To compute the effective address, we first add together `d` and `imm`.
/// This is then used to look up a `u16` in the zero bank. This value is then
/// used to offset the DBR, and then the sum of that with `y` is the address.
/// ```
/// let addr = (dbr ++ *(d + imm)) + y;
/// ```
/// # Syntax
/// ```text
/// xyz ($12), y
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectIndirectY {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct indirect long addressing.
///
/// To compuite the effective address, we first add together `d` and `imm`.
/// This is then used to look up a `u24` in the zero bank, which is the
/// address.
/// ```text
/// let addr = *(d + imm);
/// ```
/// # Syntax
/// ```text
/// xyz [$12]
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectIndirectLong {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// Direct `y`-indexed indirect long addressing.
///
/// To compute the effective address, we first add together `d` and `imm`.
/// This is then used to look up a `u24` in the zero bank. The sum of this
/// value with `y` is the address.
/// ```
/// let addr = *(d + imm) + y;
/// ```
/// # Syntax
/// ```text
/// xyz [$12], y
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DirectIndirectLongY {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// An 8-bit or 16-bit immediate value.
///
/// # Syntax
/// ```text
/// xyz #$12
/// xyz #$1234
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Imm {
  /// An 8-bit immediate.
  U8(SymOr<u8>),
  /// A 16-bit immediate.
  U16(SymOr<u16>),
}

/// `pc`-relative addressing.
///
/// The effective address is computed by first sign-extending `imm` to 16
/// bits, and adding it to `pc`. The result is concatenated with the PBR.
///
/// The value `pc` takes on is that of the *next* instruction to execute.
/// ```text
/// let addr = pbr ++ (pc + sext(imm));
/// ```
/// # Syntax
/// ```text
/// xyz local_label
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PcRel {
  /// The immediate operand.
  imm: SymOr<i8>,
}

/// `pc`-relative long addressing.
///
/// The effective address is computed by adding `imm` to `pc`. The result
/// bits, and adding it to `pc`. The result is concatenated with the PBR.
///
/// The value `pc` takes on is that of the *next* instruction to execute.
/// ```text
/// let addr = pbr ++ (pc + sext(imm));
/// ```
/// # Syntax
/// ```text
/// xyz far_label
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PcRelLong {
  /// The immediate operand.
  imm: SymOr<i16>,
}

/// `s`-relative addressing.
///
/// The effective address is simply the sum of `s` and `imm`, in the zero
/// bank (where the stack normally lives).
/// ```text
/// let addr = s + imm;
/// ```
/// # Syntax
/// ```text
/// xyz $12, s
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct StackRel {
  /// The immediate operand.
  imm: SymOr<u8>,
}

/// `s`-relative, indirect `y`-indexed addressing.
///
/// The effective address computed by first summing `s` and `imm`; this is
/// used to look up a `u16` in the zero bank. This value is used to offset the
/// DBR, which is then added to `y`, forming the address.
/// ```text
/// let addr = (dbr ++ *(s + imm)) + y;
/// ```
/// # Syntax
/// ```text
/// xyz ($12, s), y
/// ```
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct StackRelIndirectY {
  /// The immediate operand.
  imm: SymOr<u8>,
}
