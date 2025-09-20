use std::error::Error;
use std::ffi::OsString;
use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;

use clap::ArgAction::{Set, SetTrue};
use clap::Parser;
use tracing::{Level, event, span};
use tracing_subscriber::prelude::*;

use assembler::*;

// Thanks to Google for allowing this code to be open-sourced.  I
// generally prefer to correspond about this project using my
// personal email address rather than my work one, though.
const AUTHOR: &str = "James Youngman <james@youngman.org>";

/// Assembler for the historical TX-2 computer
#[derive(Parser, Debug)]
#[clap(author = AUTHOR, version, about, long_about = None)]
struct Cli {
    /// File from which assembly source is read.
    #[clap(action=Set)]
    input: OsString,

    /// File to which assembler output is written
    #[clap(action = Set, short = 'o', long)]
    output: OsString,

    /// When set, list the assembler output (analogous to the listing
    /// produced by the M4 assembler's LIST command).
    #[clap(action = SetTrue, long)]
    list: bool,
}

#[derive(Debug)]
enum Fail {
    /// We iniitialised the assembler but then it fails.
    AsmFail(AssemblerFailure),
    /// We were not able to correctly initialise the assembler.
    InitialisationFailure(String),
}

impl Display for Fail {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Fail::AsmFail(assembler_failure) => assembler_failure.fmt(f),
            Fail::InitialisationFailure(msg) => f.write_str(msg.as_str()),
        }
    }
}

impl Error for Fail {}
fn run_asembler() -> Result<(), Fail> {
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
            return Err(Fail::InitialisationFailure(format!(
                "failed to initialise tracing filter (perhaps there is a problem with environment variables): {e}"
            )));
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let span = span!(Level::ERROR, "assemble", input=?cli.input, output=?cli.output);
    let _enter = span.enter();
    let output_path = PathBuf::from(cli.output);
    let options: OutputOptions = OutputOptions { list: cli.list };
    let result = assemble_file(&cli.input, &output_path, options).map_err(Fail::AsmFail);
    if let Err(e) = &result {
        event!(Level::ERROR, "assembly failed: {:?}", e);
    } else {
        event!(Level::INFO, "assembly succeeded");
    }
    result
}

fn main() {
    unsafe { backtrace_on_stack_overflow::enable() };

    match run_asembler() {
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
