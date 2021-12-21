use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::fs::OpenOptions;
use std::io::Error as IoError;
use std::io::{BufRead, BufReader};

use clap::{App, Arg};
use tracing::{event, span, Level};
use tracing_subscriber::prelude::*;

#[derive(Debug)]
enum AssemblerFailure {
    Unimplemented(String),
    IoErrorOnInput {
        filename: OsString,
        error: IoError,
        line_number: Option<usize>,
    },
}

fn write_os_string(f: &mut Formatter<'_>, s: &OsStr) -> Result<(), fmt::Error> {
    match s.to_str() {
        Some(unicode_name) => f.write_str(unicode_name),
        None => write!(
            f,
            "{} (some non-Unicode characters changed to make it printable)",
            s.to_string_lossy(),
        ),
    }
}

impl Display for AssemblerFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            AssemblerFailure::Unimplemented(explanation) => {
                write!(f, "use of unimplemented feature: {}", explanation)
            }
            AssemblerFailure::IoErrorOnInput {
                filename,
                error,
                line_number,
            } => {
                f.write_str("I/O error reading input file ")?;
                write_os_string(f, filename)?;
                if let Some(n) = line_number {
                    write!(f, " at line {}", n)?;
                }
                write!(f, ": {}", error)
            }
        }
    }
}

impl Error for AssemblerFailure {}

#[derive(Debug)]
enum Fail {
    AsmFail(AssemblerFailure),
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

#[derive(Debug)]
enum ProgramInstruction {}

#[derive(Debug)]
struct SymbolTable {}

impl SymbolTable {
    fn new() -> SymbolTable {
        SymbolTable {}
    }
}

fn assemble_line(
    _line: &str,
    _symtab: &mut SymbolTable,
) -> Result<Option<ProgramInstruction>, AssemblerFailure> {
    Err(AssemblerFailure::Unimplemented(
        "I should write this part".to_string(),
    ))
}

fn assemble_pass1(
    lines: &[String],
    symtab: &mut SymbolTable,
) -> Result<Vec<ProgramInstruction>, AssemblerFailure> {
    lines
        .iter()
        .filter_map(|line| match assemble_line(line, symtab) {
            Ok(None) => None,
            Ok(Some(instr)) => Some(Ok(instr)),
            Err(e) => Some(Err(e)),
        })
        .collect()
}

fn assemble_file(input_file: &OsStr, _output_file: &OsStr) -> Result<(), AssemblerFailure> {
    let input = OpenOptions::new()
        .read(true)
        .open(input_file)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file.to_owned(),
            error: e,
            line_number: None,
        })?;
    let mut source_lines: Vec<String> = Vec::new();
    for (line, input_item) in BufReader::new(input)
        .lines()
        .enumerate()
        .map(|(n, sl)| (n + 1, sl))
    {
        match input_item {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file.to_owned(),
                    error: e,
                    line_number: Some(line),
                });
            }
            Ok(source_line) => {
                source_lines.push(source_line);
            }
        }
    }

    let mut symtab = SymbolTable::new();
    let pass1_output: Vec<ProgramInstruction> = assemble_pass1(&source_lines, &mut symtab)?;
    drop(pass1_output);
    todo!()
}

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
