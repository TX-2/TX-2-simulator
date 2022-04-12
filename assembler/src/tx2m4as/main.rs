use std::ffi::OsString;

use clap::Parser;
use tracing::{event, span, Level};
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
    /// File from which assembly source is read
    input: OsString,

    /// File to which assembler output is written
    #[clap(short = 'o', long)]
    output: OsString,
}

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
            return Err(Fail::InitialisationFailure(
		format!("failed to initialise tracing filter (perhaps there is a problem with environment variables): {}", e)));
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let span = span!(Level::ERROR, "assemble", input=?cli.input, output=?cli.output);
    let _enter = span.enter();
    let result = assemble_file(&cli.input, &cli.output).map_err(Fail::AsmFail);
    if let Err(e) = &result {
        event!(Level::ERROR, "assembly failed: {:?}", e);
    } else {
        event!(Level::INFO, "assembly succeeded");
    }
    result
}

fn main() {
    match run_asembler() {
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
