//! Instruction mnemonics for the 65816 ISA.

use std::str::FromStr;

/// The error returned when parsing a `Mnemonic` from a string.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct MnemonicParseError;

/// A macro for generating the `Mnemonic` enum.
macro_rules! mnemonics {
  ($($(#[$attr:meta])* $name:ident: $mne:literal,)*) => {
    /// A 65816 mnemonic, representing a class of instructions.
    ///
    /// A `Mnemonic` represents a class of instructions with similar
    /// behavior but potentially many addressing modes, such as the fifteen
    /// instructions starting with `adc`.
    ///
    /// This enum also provides documentation on what the instructions
    /// represented by those mnemonics represent.
    ///
    /// See [`Instruction`](struct.Instruction.html) for a list of all
    /// *instructions*, which correspond to 65816 opcodes.
    #[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
    pub enum Mnemonic {
      $($(#[$attr])* $name,)*
    }

    impl Mnemonic {
      /// Gets the name of this mnemonic.
      pub fn name(self) -> &'static str {
        match self {
          $(Self::$name => $mne,)*
        }
      }

      /// Gets the mnemonic with the given name, if there is one.
      ///
      /// Matching is case-insensitive: `"ADC"`, `"adc"`, and `"AdC"` will all
      /// return `Mnemonic::Adc`.
      pub fn from_name(name: &str) -> Option<Self> {
        $(if name.eq_ignore_ascii_case($mne) {
          return Some(Mnemonic::$name)
        })*

        None
      }
    }
  };
}

impl FromStr for Mnemonic {
  type Err = MnemonicParseError;
  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Self::from_name(s).ok_or(MnemonicParseError)
  }
}

mnemonics! {
  /// No operation.
  ///
  /// Does nothing.
  Nop: "nop",

  /// Add with carry.
  ///
  /// Adds the byte located at the effective address to the accumulator, taking
  /// into account the carry flag.
  /// ```text
  /// a += *addr;
  /// ```
  Adc: "adc",
  /// Subtract with borrow.
  ///
  /// Subtracts the byte located at the effective address from the accumulator,
  /// taking into account the carry flag.
  /// ```text
  /// a -= *addr;
  /// ```
  Sbc: "sbc",
  /// Bitwise AND.
  ///
  /// ANDs the addumulator with the byte located at the effective address.
  /// ```text
  /// a &= *addr;
  /// ```
  And: "and",
  /// Bitwise XOR.
  ///
  /// XORs the addumulator with the byte located at the effective address.
  /// ```text
  /// a ^= *addr;
  /// ```
  Eor: "eor",
  /// Bitwise OR.
  ///
  /// ORs the addumulator with the byte located at the effective address.
  /// ```text
  /// a |= *addr;
  /// ```
  Ora: "ora",
  /// Arithmetic left shift.
  ///
  /// Shifts the value in the effective address by 1, dumping the top
  /// bit into the carry flag.
  /// ```text
  /// carry = top_bit(*addr);
  /// *addr <<= 1;
  /// ```
  Asl: "asl",
  /// Logical right shift.
  ///
  /// Shifts the value in the effective address by 1, dumping the bottom
  /// bit into the carry flag.
  /// ```text
  /// carry = bottom_bit(*addr);
  /// *addr >>= 1;
  /// ```
  Lsr: "lsr",
  /// Rotate left.
  ///
  /// Performs an `n + 1`-bit rotation of the value at the effective address,
  /// using the carry flag as the extra bit. The length of the rotation depends
  /// on the `m` bit.
  Rol: "rol",
  /// Rotate right.
  ///
  /// Performs an `n + 1`-bit rotation of the value at the effective address,
  /// using the carry flag as the extra bit. The length of the rotation depends
  /// on the `m` bit.
  Ror: "ror",
  /// Compare accumulator.
  ///
  /// Subtractrs the value at the effective address from the accumulator,
  /// discarding the result but setting flags as if it had happened.
  /// ```text
  /// let _ = a - *addr;
  /// ```
  Cmp: "cmp",
  /// Compare `x` index.
  ///
  /// Much like `cmp`, except with respect to `x` rather than `a`.
  /// ```text
  /// let _ = x - *addr;
  /// ```
  Cpx: "cpx",
  /// Compare `y` index.
  ///
  /// Much like `cmp`, except with respect to `y` rather than `a`.
  /// ```text
  /// let _ = y - *addr;
  /// ```
  Cpy: "cpy",
  /// Decrement accumulator.
  ///
  /// Decrements the accumulator by one, ignoring the carry flag.
  /// ```text
  /// a -= 1;
  /// ```
  Dec: "dec",
  /// Decrement `x` index.
  ///
  /// Decrements `x` by one, ignoring the carry flag.
  /// ```text
  /// x -= 1;
  /// ```
  Dex: "dex",
  /// Decrement `y` index.
  ///
  /// Decrements `y` by one, ignoring the carry flag.
  /// ```text
  /// y -= 1;
  /// ```
  Dey: "dey",
  /// Increment accumulator.
  ///
  /// Increments the accumulator by one, ignoring the carry flag.
  /// ```text
  /// a += 1;
  /// ```
  Inc: "inc",
  /// Increment `x` index.
  ///
  /// Increments `x` by one, ignoring the carry flag.
  /// ```text
  /// x += 1;
  /// ```
  Inx: "inx",
  /// Increment `y` index.
  ///
  /// Increments `y` by one, ignoring the carry flag.
  /// ```text
  /// y += 1;
  /// ```
  Iny: "iny",

  /// Load accumulator from memory.
  ///
  /// Loads a value from memory onto the accumulator. The width of the load
  /// is equal to the current width of the accumulator.
  /// ```text
  /// a = *addr;
  /// ```
  Lda: "lda",
  /// Load `x` from memory.
  ///
  /// Loads a value from memory onto `x`. The width of the load is equal to the
  /// current width of `x`.
  /// ```text
  /// x = *addr;
  /// ```
  Ldx: "ldx",
  /// Load `y` from memory.
  ///
  /// Loads a value from memory onto `y`. The width of the load is equal to the
  /// current width of `y`.
  /// ```text
  /// y = *addr;
  /// ```
  Ldy: "ldy",
  /// Store accumulator to memory.
  ///
  /// Store the accumulator value to memory. The width of the store
  /// is equal to the current width of the accumulator.
  /// ```text
  /// *addr = a;
  /// ```
  Sta: "sta",
  /// Store `x` to memory.
  ///
  /// Store `x` to memory. The width of the load is equal to
  /// the current width of `x`.
  /// ```text
  /// *addr = x;
  /// ```
  Stx: "stx",
  /// Store `y` to memory.
  ///
  /// Store `y` to memory. The width of the load is equal to
  /// the current width of `y`.
  /// ```text
  /// *addr = y;
  /// ```
  Sty: "sty",
  /// Store zero to memory.
  ///
  /// Zeroes the value at the effective address. The width of the value depends
  /// on the `m` flag.
  /// ```text
  /// *addr = 0;
  /// ```
  Stz: "stz",
  /// Transfer accumulator to `x`.
  ///
  /// Moves `a` to `x`.
  /// ```text
  /// x = a;
  /// ```
  Tax: "tax",
  /// Transfer `x` to accumulator.
  ///
  /// Move `a` to `x`.
  /// ```text
  /// a = x;
  /// ```
  Txa: "txa",
  /// Transfer accumulator to `y`.
  ///
  /// Moves `a` to `y`.
  /// ```text
  /// y = a;
  /// ```
  Tay: "tay",
  /// Transfer `y` to accumulator.
  ///
  /// Moves `y` to `a`.
  /// ```text
  /// a = y;
  /// ```
  Tya: "tya",
  /// Transfer accumulator to DPR.
  ///
  /// Moves `a` to `d`, always treating `a` as 16-bit.
  /// ```text
  /// d = a;
  /// ```
  Tcd: "tcd",
  /// Transfer DPR to accumulator.
  ///
  /// Moves `d` to `a`, always treating `a` as 16-bit.
  /// ```text
  /// a = d;
  /// ```
  Tdc: "tdc",
  /// Transfer accumulator to stack pointer.
  ///
  /// Moves `a` to `s`, always treating `a` as 16-bit.
  /// ```text
  /// s = a;
  /// ```
  Tcs: "tcs",
  /// Transfer stack pointer to accumulator.
  ///
  /// Moves `s` to `a`, always treating `a` as 16-bit.
  /// ```text
  /// a = s;
  /// ```
  Tsc: "tsc",
  /// Transfer stack pointer to `x`.
  ///
  /// Moves `s` to `x`.
  /// ```text
  /// a = s;
  /// ```
  Tsx: "tsx",
  /// Transfer `x` to stack pointer.
  ///
  /// Move `x` to `s`.
  /// ```text
  /// s = x;
  /// ```
  Txs: "txs",
  /// Transfer `x` to `y`.
  ///
  /// Move `x` to `y`.
  /// ```text
  /// y = x;
  /// ```
  Txy: "txy",
  /// Transfer `y` to `x`.
  ///
  /// Move `y` to `x`.
  /// ```text
  /// x = y;
  /// ```
  Tyx: "tyx",
  /// Exchange accumulators.
  ///
  /// Performs an endianness swap on `a`.
  /// ```text
  /// a = byte_swap(a);
  /// ```
  Xba: "xba",

  /// Block move next.
  ///
  /// Performs a `memmove()` of blocks of memory across two banks of memory,
  /// using `x`, `y`, and `a` as the source, destination, and length. The blocks
  /// are specified by the two operands.
  /// ```text
  /// while a != 0xffff {
  ///   *(destbk ++ y) = *(srcbk ++ x)
  ///   x += 1;
  ///   y += 1;
  ///   a -= 1;
  /// }
  /// ```
  Mvn: "mvn",
  /// Block move previous.
  ///
  /// Exactly like `mvn`, except `x` and `y` point to the ends, rather than the
  /// starts, of the blocks to move.
  /// ```text
  /// while a != 0xffff {
  ///   *(destbk ++ y) = *(srcbk ++ x)
  ///   x -= 1;
  ///   y -= 1;
  ///   a -= 1;
  /// }
  /// ```
  Mvp: "mvp",

  /// Push effective absolute address.
  ///
  /// Pushes a 16-bit immediate onto the stack.
  /// ```text
  /// *s = addr;
  /// s -= 2;
  /// ```
  Pea: "pea",
  /// Push effective indirect address.
  ///
  /// Pushes a 16-bit value located at the effective address.
  /// ```text
  /// *s = *addr;
  /// s -= 2;
  /// ```
  Pei: "pei",
  /// Push `pc`-relative indirect address.
  ///
  /// Push a 16-bit value located at an immediate displacement from
  /// `pc`. `pc` takes on the value of the *next* instruction.
  /// ```text
  /// *s = *(pc + addr);
  /// s -= 2;
  /// ```
  Per: "per",
  /// Push accumulator.
  ///
  /// Pushes the accumulator onto the stack. The number of bytes pushed
  /// depends on the size of the accumulator at the time.
  /// ```text
  /// *s = a;
  /// s -= size_of(a);
  /// ```
  Pha: "pha",
  /// Push DBR.
  ///
  /// Pushes the single byte of the DBR onto the stack.
  /// ```text
  /// *s = dbr;
  /// s -= 1;
  /// ```
  Phb: "phb",
  /// Push DPR.
  ///
  /// Pushes the direct page register onto the stack.
  /// ```text
  /// *s = d;
  /// s -= 2;
  /// ```
  Phd: "phd",
  /// Push PBR.
  ///
  /// Pushes the single byte of the PBR onto the stack.
  /// ```text
  /// *s = pbr;
  /// s -= 2;
  /// ```
  Phk: "phk",
  /// Push status.
  ///
  /// Pushes the status register onto the stack.
  /// ```text
  /// *s = status;
  /// s -= 2;
  /// ```
  Php: "php",
  /// Push `x` index.
  ///
  /// Pushes `x` onto the stack. The number of bytes pushed depends on the size
  ///  of `x` at the time.
  /// ```text
  /// *s = x;
  /// s -= size_of(x);
  /// ```
  Phx: "phx",
  /// Push `y` index.
  ///
  /// Pushes `y` onto the stack. The number of bytes pushed depends on the size
  ///  of `y` at the time.
  /// ```text
  /// *s = y;
  /// s -= size_of(y);
  /// ```
  Phy: "phy",

  /// Pop accumulator.
  ///
  /// Pops the accumulator from the stack. The number of bytes popped
  /// depends on the size of the accumulator at the time.
  /// ```text
  /// a = *s;
  /// s += size_of(a);
  /// ```
  Pla: "pla",
  /// Pop DBR.
  ///
  /// Pops the single byte of the DBR from the stack.
  /// ```text
  /// dbr = *s;
  /// s += 1;
  /// ```
  Plb: "plb",
  /// Pop DPR.
  ///
  /// Pops the direct page register from the stack.
  /// ```text
  /// d = *s;
  /// s += 2;
  /// ```
  Pld: "pld",
  /// Pop status.
  ///
  /// Pops the status register from the stack.
  /// ```text
  /// status = *s;
  /// s += 2;
  /// ```
  Plp: "plp",
  /// Pop `x` index.
  ///
  /// Pops `x` form the stack. The number of bytes popped depends on the size
  ///  of `x` at the time.
  /// ```text
  /// x = *s;
  /// s += size_of(x);
  /// ```
  Plx: "plx",
  /// Pop `y` index.
  ///
  /// Pops `y` from the stack. The number of bytes popped depends on the size
  ///  of `y` at the time.
  /// ```text
  /// y = *s;
  /// s += size_of(y);
  /// ```
  Ply: "ply",

  /// Branch if carry set.
  ///
  /// Performs a near jump if the carry flag is set.
  Bcs: "bcs",
  /// Branch if carry clear.
  ///
  /// Performs a near jump if the carry flag is clear.
  Bcc: "bcc",
  /// Branch if equal.
  ///
  /// Performs a near jump if the zero flag is set.
  Beq: "beq",
  /// Branch if not equal.
  ///
  /// Performs a near jump if the zero flag is clear.
  Bne: "bne",
  /// Branch if minus.
  ///
  /// Performs a near jump if the negative flag is set.
  Bmi: "bmi",
  /// Branch if plus.
  ///
  /// Performs a near jump if the negative flag is clear.
  Bpl: "bpl",
  /// Branch if overflow set.
  ///
  /// Performs a near jump if the overflow flag is set.
  Bvs: "bvs",
  /// Branch if overflow clear.
  ///
  /// Performs a near jump if the overflow flag is clear.
  Bvc: "bvc",
  /// Branch always.
  ///
  /// Performs a near jump; essentially a `pc`-relative same-bank jump.
  Bra: "bra",
  /// Branch always long.
  ///
  /// Like `bra`, but with a two-byte displacement.
  Brl: "brl",

  /// Jump.
  ///
  /// Performs an absolute jump.
  Jmp: "jmp",
  /// Long jump.
  ///
  /// Performs an absolute long jump.
  Jml: "jml",
  /// Jump to subroutine.
  ///
  /// Perfomrs an absolute jump, pushing a return address onto the stack.
  Jsr: "jsr",
  /// Long jump to subroutine.
  ///
  /// Performs an absolute long jump, pushing a return address onto the stack.
  Jsl: "jsl",
  /// Return from interrupt.
  ///
  /// Long jumps back to a place where an interrupt occured, popping off flags
  /// and a long return address.
  Rti: "rti",
  /// Return from subroutine.
  ///
  /// Jumps back to the instruction right after a `jsr` instruction, popping off
  /// a return address.
  Rts: "rts",
  /// Long return from subroutine.
  ///
  /// Long jumps back to the instruction right after a `jsl` instrution,
  /// popping off a long return address.
  Rtl: "rtl",

  /// Clear carry flag.
  ///
  /// Clears the carry flag.
  Clc: "clc",
  /// Set carry flag.
  ///
  /// Sets the carry flag.
  Sec: "sec",
  /// Clear decimal flag.
  ///
  /// Clears the decimal flag.
  Cld: "cld",
  /// Set decimal flag.
  ///
  /// Sets the decimal flag.
  Sed: "sed",
  /// Clear interrupt-disable flag.
  ///
  /// Clears the interrupt-disable flag.
  Cli: "cli",
  /// Set interrupt-disable flag.
  ///
  /// Sets the interrupt-disable flag.
  Sei: "sei",
  /// Clear overflow flag.
  ///
  /// Clears the overflow flag.
  Clv: "clv",

  /// Reset status bits.
  ///
  /// Clears bits in the status flag according to bits set in the given
  /// immediate.
  /// ```
  /// status &= !imm;
  /// ```
  Rep: "rep",
  /// Set status bits.
  ///
  /// Sets bits in the status flag according to bits set in the given
  /// immediate.
  /// ```
  /// status |= imm;
  /// ```
  Sep: "sep",

  /// Exchange carry and emulation.
  ///
  /// Swaps the carry flag with the "phantom" emulation flag. This instruction
  /// is the mechanism for switching between the native and emulation modes.
  Xce: "xcd",

  /// Test bits, simlar to the x86 `test` instruction.
  ///
  /// Sets the negative and overflow flags to the value of the highest and
  /// second highest bits of the value at the effective address,
  /// respectively. Whether the value is a `u8` or a `u16` depends on whether
  /// the `m` flag is set. It then ANDs the accumulator with the operand;
  /// the zero flag is set when this computation is zero (though it does)
  /// not clobber `a`.
  Bit: "bit",
  /// Test and reset bits.
  ///
  /// Unsets bits at the effective address according to those set in the
  /// accumulator.
  ///
  /// The zero flag is set if, before the operaton, `a | *addr` is zero.
  /// ```
  /// *addr = *addr & !a;
  /// ```
  Trb: "trb",
  /// Test and set bits.
  ///
  /// Sets bits at the effective address according to those set in the
  /// accumulator.
  ///
  /// The zero flag is set if, before the operaton, `a | *addr` is zero.
  /// ```
  /// *addr = *addr | !a;
  /// ```
  Tsb: "tsb",

  /// Software break.
  ///
  /// Force a software interrupt. This pushes a return address onto the stack
  /// and jumps to the value in the interrupt vector at `$00ffe6` in native mode
  /// or at `$fffe` in emulation mode.
  ///
  /// Note that, in spite of being a one-byte instruction, the return address is
  /// two bytes after this instruction.
  Brk: "brk",
  /// Coprocessor enable.
  ///
  /// Similar to `brk`, except:
  /// - The interrupt vector used is at `$00ffe4` and `$fff4` in native and
  ///   emulated mode.
  /// - This instruction may be trapped by a coprocessor, instead.
  /// - It *must* be followed by a signature byte.
  Cop: "cop",
  /// Stop the processor.
  ///
  /// This instruction causes execution to cease until the reset pin is pulled
  /// low, at which point the processor wakes back up and jumps to the reset
  /// handler.
  Stp: "stp",
  /// Wait for interrupt.
  ///
  /// Put the processor to sleep until an interrupt is serviced.
  Wai: "wai",

  /// Reserved instruction.
  Wdm: "wdm",
}
