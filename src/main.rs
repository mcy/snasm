//! SNASM driver.

#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

use std::fs::File;
use std::io::Read as _;
use std::io::Write as _;
use std::process::exit;

use structopt::StructOpt;

use snasm::syn::src::Source;
use snasm::asm;
use snasm::link;
use snasm::rom::LoRom;

mod exit_code {
  pub const IO_ERROR: i32 = 2;
  pub const BAD_FORMAT: i32 = 100;
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
  /// Format source files. Returns non-zero if files are unformatted.
  Format {
    /// Modify files in-place with their formatted equivalents.
    #[structopt(short = "i", long)]
    in_place: bool,
    
    /// Files to check for formatting.
    files: Vec<String>,
  },

  /// Builds a ROM by assembling the given files.
  Build {
    /// File to output the completed ROM to.
    #[structopt(short = "o", long, default_value = "rom.smc")]
    output: String,

    /// Skips linking and instead prints a textual representation of the
    /// assembled object files.
    #[structopt(long)]
    dump_objects: bool,

    /// Files to assemble and link.
    files: Vec<String>,
  }
}

fn read_or_die(path: &str) -> String {
  match File::open(path) {
    Ok(mut f) => {
      let mut text = String::new();
      if let Err(e) = f.read_to_string(&mut text) {
        eprintln!("could not read {}: {}", path, e);
        exit(exit_code::IO_ERROR)
      }
      text
    },
    Err(e) => {
      eprintln!("could not open {}: {}", path, e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn write_or_die(path: &str, data: &[u8]) {
  match File::create(path) {
    Ok(mut f) => {
      if let Err(e) = f.write_all(data) {
        eprintln!("could not write {}: {}", path, e);
        exit(exit_code::IO_ERROR)
      }
    },
    Err(e) => {
      eprintln!("could not open {}: {}", path, e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn main() {
  let cli = Cli::from_args();
  match cli.command {
    Command::Format { in_place, files } => {
      let mut was_dirty = false;
      for path in files {
        let text = read_or_die(&path);

        let source = Source::parse(Some(&path), &text).unwrap();
        let formatted = format!("{}", source);
        if text != formatted {
          was_dirty = true;
          if cli.verbose {
            eprintln!("{} was formatted incorrectly", path)
          }
          if in_place {
            write_or_die(&path, formatted.as_bytes());
          }
        }
      }

      if was_dirty {
        exit(exit_code::BAD_FORMAT)
      }
    }

    Command::Build { output, dump_objects, files } => {
      let mut file_texts = Vec::new();
      for path in files {
        let text = read_or_die(&path);
        file_texts.push((path, text));
      }

      let mut sources = Vec::new();
      for (path, text) in &file_texts {
        if cli.verbose {
          eprintln!("parsing {}", path)
        }
        let source = Source::parse(Some(path), text).unwrap();
        sources.push(source)
      }

      let mut objects = Vec::new();
      for source in &sources {
        if cli.verbose {
          eprintln!("assembling {}", source.file_name().unwrap())
        }
        let object = asm::assemble(source).unwrap();
        objects.push(object);
      }

      if dump_objects {
        for object in objects {
          println!("; {}", object.name().unwrap());
          object.dump(std::io::stdout()).unwrap()
        }
        return
      }

      if cli.verbose {
        eprintln!("linking")
      }
      let mut rom = LoRom::new();
      link::link(&mut rom, &mut objects).unwrap();
      write_or_die(&output, &mut rom.into_bytes());
    }
  }
}
