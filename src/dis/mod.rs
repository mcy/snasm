//! The SNASM disassembler, for dismantling ROMs into object files.

#![allow(missing_docs)]
#![allow(unused)]

use crate::obj::Object;
use crate::rom::Rom;

pub mod meta;

pub fn disassemble<'asm, 'rom>(rom: &'rom dyn Rom, metadata: &'asm meta::Metadata) -> Vec<Object<'asm>> {
  let mut objects = Vec::with_capacity(metadata.files.len());
    
    for file in &metadata.files {
      let mut object = Object::new(&file.name);
      for region in &file.blocks {
        let block = object.new_block(region.start);
        for i in 0..region.offsets.len() {
          let offset = region.offsets[i];
          let start = offset.start as usize;
          let end = region
            .offsets
            .get(i + 1)
            .map(|offset| offset.start as usize)
            .unwrap_or(region.len as usize);

          let bytes = block.zeroed_offset(offset.ty, end - start);
          rom.read(region.start.offset(offset.start as i16), bytes);
        }
      }
      objects.push(object);
    }

    objects
}