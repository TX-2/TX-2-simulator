#![deny(unsafe_code)]
use std::ffi::OsString;

use clap::ArgAction::Set;
use clap::Parser;
use tracing::{Level, span};
use tracing_subscriber::prelude::*;

use assembler::{DisassemblerFailure, disassemble_file};

// Thanks to Google for allowing this code to be open-sourced.  I
// generally prefer to correspond about this project using my
// personal email address rather than my work one, though.
const AUTHOR: &str = "James Youngman <james@youngman.org>";
const ABOUT: &str = "Disassembler for TX-2 punched-tape image files";

/// Disassembler for punched-tape binaries for the historical TX-2 computer
#[derive(Parser, Debug)]
#[clap(author = AUTHOR, version, about=ABOUT, long_about = None)]
struct Cli {
    /// File from which the binary program (punched-tape image) is
    /// read
    #[clap(action=Set)]
    input: OsString,
}

fn disassemble() -> Result<(), DisassemblerFailure> {
    let cli = Cli::parse();
    // See
    // https://docs.rs/tracing-subscriber/0.2.19/tracing_subscriber/fmt/index.html#filtering-events-with-environment-variables
    // for instructions on how to select which trace messages get
    // printed.
    let fmt_layer = tracing_subscriber::fmt::layer().with_target(true);
    let filter_layer = match tracing_subscriber::EnvFilter::try_from_default_env()
        .or_else(|_| tracing_subscriber::EnvFilter::try_new("info"))
    {
        Err(e) => {
            return Err(DisassemblerFailure::Generic(format!(
                "failed to initialise tracing filter (perhaps there is a problem with environment variables): {e}"
            )));
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let span = span!(Level::ERROR, "disassemble", input=?cli.input);
    let _enter = span.enter();

    let stderr = std::io::stderr();
    let mut stderr_handle = stderr.lock();

    let stdout = std::io::stdout();
    let mut stdout_handle = stdout.lock();

    disassemble_file(&cli.input, &mut stdout_handle, &mut stderr_handle)
}

fn main() {
    match disassemble() {
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
