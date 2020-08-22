//! The SNASM disassembler, for dismantling ROMs into object files.

#![allow(missing_docs)]
#![allow(unused)]

use crate::obj::dbg::Metadata;
use crate::obj::Object;
use crate::rom::Rom;

pub fn disassemble<'asm, 'rom>(
  rom: &'rom dyn Rom,
  metadata: &'asm Metadata,
) -> Vec<Object<'asm>> {
  let mut objects = Vec::with_capacity(metadata.files.len());

  for file in &metadata.files {
    let mut object = Object::new(&file.name);
    for region in &file.blocks {
      let block = object.new_block(region.start);
      for offset in &region.offsets {
        let bytes = block.zeroed_offset(offset.ty, offset.len);
        rom.read(region.start.offset(offset.start as i16), bytes);
      }
    }
    objects.push(object);
  }

  objects
}
