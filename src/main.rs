//! SNASM, a SNES assembler/disassembler and patch generation tool.

#![deny(missing_docs)]
#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

pub mod asm;
pub mod int;
pub mod isa;
pub mod link;
pub mod obj;
pub mod rom;
pub mod syn;

fn main() {
  let files = vec![
    (
      "foo.S",
      r#"
    .org $808000
    .extern bar
    
    
    foo.table:
    .global foo.table
    .fill 20, $ff

    foo.code:
      jsr bar
    1:
      jmp 1b"#,
    ),
    (
      "bar.S",
      r#"
    .org $809000
    .extern foo.table

    bar:
    .global bar
      adc foo.table
      rts"#,
    ),
  ];

  let asts = files
    .iter()
    .map(|&(name, text)| syn::src::Source::parse(Some(name), text).unwrap())
    .collect::<Vec<_>>();
  for ast in &asts {
    println!("--- {}", ast.file_name().unwrap());
    println!("{}---", ast);
    println!("");
  }

  let mut objs = asts
    .iter()
    .map(|src| asm::assemble(src).unwrap())
    .collect::<Vec<_>>();
  for obj in &objs {
    println!("--- {}.o", obj.name().unwrap());
    let _ = obj.dump(std::io::stdout());
    println!("---");
    println!("");
  }

  let mut rom = rom::LoRom::new();
  link::link(&mut rom, &mut objs).unwrap();
  let _ = rom.dump(std::io::stdout());
}
