//! SNASM, a SNES assembler/disassembler and patch generation tool.

#![deny(missing_docs)]
#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

pub mod int;
pub mod isa;
pub mod rom;
pub mod syn;

fn main() {
  let asm = r#"
  ; foo
  adc $ffff
  adc -129
  sbc (foo), s ; bar2
  lda.i8 #%10101010  ; bar
1:bcc 1f
  php
"#;

  let file = crate::syn::parse(None, asm).unwrap();
  syn::print(&syn::fmt::Options::default(), &file, &mut std::io::stdout())
    .unwrap();
}
