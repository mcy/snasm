//! SNASM driver.

#![deny(unused)]
#![deny(warnings)]
#![deny(unsafe_code)]

use std::fs::File;
use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::exit;

use structopt::StructOpt;

use snasm::asm;
use snasm::error::Errors;
use snasm::link;
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
  /// Format source files. Returns non-zero if files are unformatted.
  Format {
    /// Modify files in-place with their formatted equivalents.
    #[structopt(short = "i", long)]
    in_place: bool,

    /// Files to check for formatting.
    #[structopt(parse(from_os_str))]
    files: Vec<PathBuf>,
  },

  /// Builds a ROM by assembling the given files.
  Build {
    /// File to output the completed ROM to.
    #[structopt(
      short = "o",
      long,
      default_value = "rom.smc",
      parse(from_os_str)
    )]
    output: PathBuf,

    /// Skips linking and instead prints a textual representation of the
    /// assembled object files.
    #[structopt(long)]
    dump_objects: bool,

    /// Files to assemble and link.
    #[structopt(parse(from_os_str))]
    files: Vec<PathBuf>,
  },
}

fn read_or_die(path: &Path) -> String {
  match File::open(path) {
    Ok(mut f) => {
      let mut text = String::new();
      if let Err(e) = f.read_to_string(&mut text) {
        eprintln!("could not read {}: {}", path.display(), e);
        exit(exit_code::IO_ERROR)
      }
      text
    }
    Err(e) => {
      eprintln!("could not open {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn write_or_die(path: &Path, data: &[u8]) {
  match File::create(path) {
    Ok(mut f) => {
      if let Err(e) = f.write_all(data) {
        eprintln!("could not write {}: {}", path.display(), e);
        exit(exit_code::IO_ERROR)
      }
    }
    Err(e) => {
      eprintln!("could not open {}: {}", path.display(), e);
      exit(exit_code::IO_ERROR)
    }
  }
}

fn main() {
  let cli = Cli::from_args();
  match cli.command {
    Command::Format { in_place, files } => {
      let mut was_dirty = false;
      let files = files
        .into_iter()
        .map(|path| {
          let text = read_or_die(&path);
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

    Command::Build {
      output,
      dump_objects,
      files,
    } => {
      let mut file_texts = Vec::new();
      for path in files {
        let text = read_or_die(&path);
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
          println!("; {}", object.file_name().display());
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

      write_or_die(&output, &mut rom.into_bytes());
    }
  }
}
