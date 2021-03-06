//! SNASM driver.

#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

use std::fs;
use std::mem;
use std::path::Path;
use std::path::PathBuf;
use std::process::exit;

use structopt::StructOpt;

use snasm::asm;
use snasm::dis;
use snasm::error::Errors;
use snasm::link;
use snasm::obj::dbg;
use snasm::obj::Object;
use snasm::rom::LoRom;
use snasm::syn::src::Source;

mod exit_code {
  pub const IO_ERROR: i32 = 2;

  pub const PARSE_ERROR: i32 = 101;
  pub const ASSEMBLE_ERROR: i32 = 102;
  pub const LINK_ERROR: i32 = 103;

  pub const BAD_FORMAT: i32 = 200;
}

#[derive(StructOpt)]
pub struct Cli {
  /// Enablse verbose printing.
  #[structopt(short = "v", long)]
  verbose: bool,

  #[structopt(subcommand)]
  command: Command,
}

#[derive(StructOpt)]
pub enum Command {
  /// Format source files; returns non-zero if files are unformatted.
  Fmt {
    /// Modify files in-place with their formatted equivalents.
    #[structopt(short = "i", long)]
    in_place: bool,

    /// Files to check for formatting.
    #[structopt(parse(from_os_str))]
    files: Vec<PathBuf>,
  },

  /// Assembles a ROM from the given files.
  As {
    /// File to output the completed ROM to.
    #[structopt(
      short = "o",
      long,
      default_value = "rom.smc",
      parse(from_os_str)
    )]
    output: PathBuf,

    /// File to output object metadata to.
    #[structopt(short = "m", long, parse(from_os_str))]
    metadata: Option<PathBuf>,

    /// Skips linking and instead prints a textual representation of the
    /// assembled object files.
    #[structopt(long)]
    dump_objects: bool,

    /// Skips linking and instead prints a textual representation of the
    /// "interesting" parts of the ROM.
    #[structopt(long)]
    dump_binary: bool,

    /// Files to assemble and link.
    #[structopt(parse(from_os_str))]
    files: Vec<PathBuf>,
  },

  /// Disassembles a ROM using supplied metadata.
  Dis {
    /// The ROM to disassemble.
    #[structopt(short = "i", long, parse(from_os_str))]
    input: PathBuf,

    /// The metadata describing how to disassemble the ROM.
    #[structopt(short = "m", long, parse(from_os_str))]
    metadata: PathBuf,

    /// The directory to output disassembled files to.
    #[structopt(short = "o", long, default_value = ".", parse(from_os_str))]
    output_dir: PathBuf,

    /// Skips removing 8K of zeroes at the start of the ROM, if they are
    /// present.
    #[structopt(long)]
    preserve_smc_header: bool,

    /// Skips disassembly and instead prints a textual representation of the
    /// recovered object files.
    #[structopt(long)]
    dump_objects: bool,
  },
}

fn read_utf8_or_die(path: &Path) -> String {
  match fs::read_to_string(path) {
    Ok(text) => text,
    Err(e) => {
      eprintln!("could not read {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn read_json_or_die<T: serde::de::DeserializeOwned>(path: &Path) -> T {
  match json5::from_str(&read_utf8_or_die(path)) {
    Ok(x) => x,
    Err(e) => {
      eprintln!("could not parse {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn read_or_die(path: &Path) -> Vec<u8> {
  match fs::read(path) {
    Ok(text) => text,
    Err(e) => {
      eprintln!("could not read {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn write_json_or_die<T: serde::Serialize>(path: &Path, val: &T) {
  let text = match json5::to_string(val) {
    Ok(text) => text,
    Err(e) => {
      eprintln!("could not serialize {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  };
  write_or_die(path, text.as_bytes());
}

fn write_or_die(path: &Path, data: &[u8]) {
  if let Err(e) = fs::write(path, data) {
    eprintln!("could not write {}: {}", path.display(), e);
    exit(exit_code::IO_ERROR)
  }
}

fn ensure_dir_or_die(path: &Path) {
  if !path.exists() {
    if let Err(e) = fs::create_dir_all(path) {
      eprintln!("could not mkdir {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }

  if !path.is_dir() {
    eprintln!("expected directory, got {}", path.display());
    exit(exit_code::IO_ERROR)
  }
}

fn main() {
  let cli = Cli::from_args();
  match cli.command {
    Command::Fmt { in_place, files } => {
      let mut was_dirty = false;
      let files = files
        .into_iter()
        .map(|path| {
          let text = read_utf8_or_die(&path);
          (path, text)
        })
        .collect::<Vec<_>>();

      let mut sources = Vec::new();
      let mut errors = Errors::new();
      for (path, text) in &files {
        match Source::parse(path, text) {
          Ok(source) => sources.push((text, source)),
          Err(e) => errors.push(e),
        }
      }
      errors.dump_and_die(exit_code::PARSE_ERROR);

      for (text, source) in sources {
        let formatted = format!("{}", source);
        if text != &formatted {
          was_dirty = true;
          if cli.verbose {
            eprintln!(
              "{} was formatted incorrectly",
              source.file_name().display()
            )
          }
          if in_place {
            write_or_die(source.file_name(), formatted.as_bytes());
          }
        }
      }

      if was_dirty {
        exit(exit_code::BAD_FORMAT)
      }
    }

    Command::As {
      output,
      metadata,
      dump_objects,
      dump_binary,
      files,
    } => {
      let mut file_texts = Vec::new();
      for path in files {
        let text = read_utf8_or_die(&path);
        file_texts.push((path, text));
      }

      let mut sources = Vec::new();
      let mut errors = Errors::new();
      for (path, text) in &file_texts {
        if cli.verbose {
          eprintln!("parsing {}", path.display())
        }
        match Source::parse(path, text) {
          Ok(source) => sources.push(source),
          Err(e) => errors.push(e),
        }
      }
      errors.dump_and_die(exit_code::PARSE_ERROR);

      let mut objects = Vec::new();
      let mut errors = Errors::new();
      for source in &sources {
        if cli.verbose {
          eprintln!("assembling {}", source.file_name().display())
        }
        match asm::assemble(source) {
          Ok(object) => objects.push(object),
          Err(e) => errors.extend(e),
        }
      }
      errors.dump_and_die(exit_code::ASSEMBLE_ERROR);

      if dump_objects {
        for object in objects {
          println!("; {}.o", object.file_name().display());
          object.dump(std::io::stdout()).unwrap();
        }
        return;
      }

      if cli.verbose {
        eprintln!("linking")
      }
      let mut rom = LoRom::new();
      if let Err(e) = link::link(&mut rom, &mut objects) {
        e.dump_and_die(exit_code::LINK_ERROR)
      }

      if dump_binary {
        rom.dump(std::io::stdout()).unwrap();
      }

      if let Some(meta_path) = metadata {
        let metadata = dbg::Metadata {
          files: objects
            .iter_mut()
            .map(|o| {
              o.simplify_debug_info();
              o.make_debug_info()
            })
            .collect(),
        };
        write_json_or_die(&meta_path, &metadata)
      }
      write_or_die(&output, &mut rom.into_bytes());
    }

    Command::Dis {
      input,
      metadata,
      output_dir,
      preserve_smc_header,
      dump_objects,
    } => {
      let mut rom_bytes = read_or_die(&input);
      // If first 0x200 bytes are mostly zero, it's a dumb header we should rip
      // out.
      if !preserve_smc_header && rom_bytes.len() >= 0x200 {
        let zeroes = (0..0x200)
          .into_iter()
          .filter(|&i| rom_bytes[i] == 0)
          .count();
        if zeroes > 0x1d0 {
          // Arbitrary constant.
          let old_bytes = mem::take(&mut rom_bytes);
          rom_bytes.resize(old_bytes.len() - 0x200, 0);
          rom_bytes.copy_from_slice(&old_bytes[0x200..]);
        }
      }

      let rom = LoRom::from_bytes(rom_bytes);

      let metadata = read_json_or_die::<dbg::Metadata>(&metadata);

      let mut objects = Vec::new();
      for file in &metadata.files {
        objects.push(Object::from_debug_info(&rom, file));
      }

      if dump_objects {
        for object in objects {
          println!("; {}.o", object.file_name().display());
          object.dump(std::io::stdout()).unwrap();
        }
        return;
      }

      let mut sources = Vec::new();
      for object in &objects {
        sources.push(dis::disassemble(object));
      }

      ensure_dir_or_die(&output_dir);
      for source in sources {
        let path = output_dir.join(source.file_name());
        ensure_dir_or_die(path.parent().unwrap());
        let text = format!("{}", source);
        write_or_die(&path, text.as_bytes());
      }
    }
  }
}
