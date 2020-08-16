//! SNASM, a SNES assembler/disassembler and patch generation tool.

#![deny(missing_docs)]
#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

pub mod assembler;

pub mod int;
pub mod isa;
pub mod rom;
pub mod syn;

fn main() {
  let asm = r#"
  ; Computes the sum of all the integers in the range a..b.
  ;
  ; ABI is (.., a, b, ra1, ra2) on the stack, with (.., sum, ?) afterwards.
  sum_of_range:
    tsc
    inc a
    tcs
    lda #0i16
    pha
    tsx
  loop:
    lda 0, s
    adc 3, s
    sta 0, s
    lda 3, s
    inc a
    cmp 2, s
    beq end
    sta 3, s
    bra loop
  end:
    lda 0, s
    sta 3, s
    tsc
    dec a
    tcs
    rtl

  .origin $900000
  main:
    ldx #5_i16
    ldy #10_i16
    jsr sum_of_range
  .extern foo
    jsr foo
"#;

  let file = crate::syn::parse(None, asm).unwrap();
  syn::print(&syn::fmt::Options::default(), &file, &mut std::io::stdout())
    .unwrap();

  let obj = match assembler::assemble(&file) {
    Ok(o) => o,
    Err(e) => panic!("{:#?}", e),
  };
  obj.dump(std::io::stdout()).unwrap();
}
