//! This program converts an octal dump of a program (as shown in the
//! right-hand columns of an assembler listing) into a tape image
//! suitable for loading into a simulated TX-2.
use std::{
    error::Error,
    ffi::OsString,
    fmt::Display,
    fs::{File, OpenOptions},
    io::{BufRead, BufReader, BufWriter},
    path::PathBuf,
};

use clap::ArgAction::Set;
use clap::Parser;
use regex::Regex;

use assembler::{Binary, BinaryChunk, write_user_program};
use base::prelude::{Address, Unsigned18Bit, Unsigned36Bit, join_halves};

const OCTAL: u32 = 8;

#[derive(Debug)]
struct Fail(String);

impl Display for Fail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl Error for Fail {}

// Thanks to Google for allowing this code to be open-sourced.  I
// generally prefer to correspond about this project using my
// personal email address rather than my work one, though.
const AUTHOR: &str = "James Youngman <james@youngman.org>";

/// Make a tape image for the historical TX-2 computer
#[derive(Parser, Debug)]
#[clap(author = AUTHOR, version, about, long_about = None)]
struct Cli {
    /// File from which the octal dump is read.
    #[clap(action=Set)]
    input: OsString,

    /// File to which assembler output is written
    #[clap(action = Set, short = 'o', long)]
    output: OsString,
}

fn read_binary(input_file: File) -> Result<Binary, Fail> {
    let pattern: &'static str = r"^\s*[|](\d+) +(\d+)[|]\s*(\d+)\s*$";
    let line_rx = match Regex::new(pattern) {
        Ok(rx) => rx,
        Err(e) => {
            return Err(Fail(format!(
                "internal error: failed to compile regular expression '{pattern}': {e}"
            )));
        }
    };
    let reader = BufReader::new(input_file);

    let mut binary: Binary = Default::default();
    let mut chunk: Option<BinaryChunk> = None;
    let mut prev_addr: Option<Unsigned18Bit> = None;

    for line_result in reader.lines() {
        let line = match line_result {
            Err(e) => {
                return Err(Fail(format!("failed to read from input file: {e}")));
            }
            Ok(line) => line,
        };
        let line = line.trim();
        if line.is_empty() {
            continue; // ignore blank lines.
        }
        let matches = match line_rx.captures(line) {
            Some(m) => m,
            None => {
                return Err(Fail(format!(
                    "input line '{line}' does not match required regular expression {pattern})"
                )));
            }
        };
        let (_, [left, right, address]) = matches.extract();
        if left.len() != 6 {
            return Err(Fail(format!(
                "input line {line} has field {left} but it should be 6 characters long"
            )));
        }
        let left: Unsigned18Bit = match u32::from_str_radix(left, OCTAL).map(|n| n.try_into()) {
            Ok(Ok(n)) => n,
            _ => {
                return Err(Fail(format!("field {left} should be an octal number")));
            }
        };
        if right.len() != 6 {
            return Err(Fail(format!(
                "input line {line} has field {right} but it should be 6 characters long"
            )));
        }
        let right: Unsigned18Bit = match u32::from_str_radix(right, OCTAL).map(|n| n.try_into()) {
            Ok(Ok(n)) => n,
            _ => {
                return Err(Fail(format!("field {right} should be an octal number")));
            }
        };
        let prev_plus_one: Option<Unsigned18Bit> = match prev_addr {
            None => None,
            Some(p) => match p.checked_add(Unsigned18Bit::ONE) {
                Some(n) => Some(n),
                None => {
                    // There could be an off-by-one error here, but
                    // it's not important, because loading a binary
                    // into V-memory (which is at the top) isn't
                    // something you should expect to work.
                    return Err(Fail("A block is too long to fit in memory".to_string()));
                }
            },
        };

        let word: Unsigned36Bit = join_halves(left, right);
        let addr: Unsigned18Bit = match u32::from_str_radix(address, OCTAL).map(|n| n.try_into()) {
            Ok(Ok(n)) => {
                if address.len() == 3 {
                    match prev_plus_one {
                        Some(p) => (p & 0o777000) | (n & 0o777),
                        None => {
                            return Err(Fail(format!(
                                "The first address field {address} should be 6 characters long"
                            )));
                        }
                    }
                } else {
                    n
                }
            }
            _ => {
                return Err(Fail(format!("field {address} should be an octal number")));
            }
        };

        let non_contiuguous = match prev_plus_one {
            None => true,
            Some(expected) => expected != addr,
        };

        if non_contiuguous && let Some(old) = chunk.take() {
            assert!(!old.is_empty());
            binary.add_chunk(old);
        }
        let ch: &mut BinaryChunk = chunk.get_or_insert_with(|| BinaryChunk {
            address: Address::from(addr),
            words: Vec::new(),
        });
        prev_addr = Some(addr);
        ch.push(word);
    }
    if let Some(current) = chunk.take()
        && !current.is_empty()
    {
        binary.add_chunk(current);
    }
    Ok(binary)
}

fn run_utility() -> Result<(), Fail> {
    let cli = Cli::parse();
    let input_file = OpenOptions::new()
        .read(true)
        .open(cli.input)
        .map_err(|e| Fail(format!("failed to open input file: {e}")))?;
    let binary = read_binary(input_file)?;

    let output_path = PathBuf::from(cli.output);
    let output_file = OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(&output_path)
        .map_err(|e| Fail(format!("failed to write output: {e}")))?;

    let mut writer = BufWriter::new(output_file);
    match write_user_program(&binary, &mut writer, &output_path) {
        Ok(()) => Ok(()),
        Err(e) => Err(Fail(e.to_string())),
    }
}

fn main() {
    match run_utility() {
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
