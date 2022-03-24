use std::ffi::OsString;

use clap::{App, Arg};
use tracing::{event, span, Level};
use tracing_subscriber::prelude::*;

use assembler::*;

fn run_asembler() -> Result<(), Fail> {
    let matches = App::new("TX-2 Assembler")
        .author("James Youngman <youngman@google.com>")
        .about("Assembler for the historic TX-2 computer")
        .arg(
            Arg::with_name("INPUT")
                .help("File containing assembly source code")
                .multiple(false)
                .required(true),
        )
        .arg(
            Arg::with_name("output-file")
                .help("File to which assembler output is written")
                .takes_value(true)
                .short("o")
                .long("output")
                .required(true),
        )
        .get_matches();

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

    let input_file: OsString = matches.value_of_os("INPUT").unwrap().to_owned();
    let output_file: OsString = matches.value_of_os("output-file").unwrap().to_owned();

    let span = span!(Level::ERROR, "assemble", input=?input_file, output=?output_file);
    let _enter = span.enter();
    let result = assemble_file(&input_file, &output_file).map_err(Fail::AsmFail);
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