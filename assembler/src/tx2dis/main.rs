#![deny(unsafe_code)]

use base::prelude::*;
use clap::ArgAction::Set;
use clap::Parser;
use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt::{self, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read};
use tracing::{span, Level};
use tracing_subscriber::prelude::*;

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

#[derive(Debug)]
enum Fail {
    ReadFailed(String),
    Generic(String),
    ShortFile,
}

impl Display for Fail {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Fail::Generic(message) | Fail::ReadFailed(message) => f.write_str(message),
            Fail::ShortFile => f.write_str("file ended unexpectedly"),
        }
    }
}

impl Error for Fail {}

fn update_sum(sum: Signed18Bit, word: Unsigned36Bit) -> Signed18Bit {
    let (left, right) = split_halves(word);
    sum.wrapping_add(right.reinterpret_as_signed())
        .wrapping_add(left.reinterpret_as_signed())
}

fn read_splayed_words<R: Read>(
    input: &mut R,
    count: usize,
    mut maybe_checksum: Option<&mut Signed18Bit>,
) -> Result<Vec<Unsigned36Bit>, Fail> {
    const SPLAY_SIZE: usize = 6;
    let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(count);
    for _ in 0..count {
        let mut w = Unsigned36Bit::ZERO;
        let mut buf: [u8; SPLAY_SIZE] = [0; SPLAY_SIZE];
        match input.read(&mut buf) {
            Ok(0) => {
                return Err(Fail::ShortFile);
            }
            Ok(nbytes) => {
                if nbytes != SPLAY_SIZE {
                    return Err(Fail::Generic(
                        "input file length should be a multiple of 6 bytes".to_string(),
                    ));
                }
                for byte in buf.into_iter() {
                    let line: Unsigned6Bit = Unsigned6Bit::try_from(byte & 0o77).unwrap();
                    w = cycle_and_splay(w, line);
                }
                match maybe_checksum {
                    Some(ref mut checksum) => {
                        **checksum = update_sum(**checksum, w);
                    }
                    None => (),
                }
                result.push(w);
            }
            Err(e) => {
                return Err(Fail::ReadFailed(e.to_string()));
            }
        }
    }
    Ok(result)
}

fn disassemble_block(mut pos: Unsigned18Bit, block: &[Unsigned36Bit]) {
    let mut is_origin: bool = true;
    for w in block.iter() {
        disassemble_word(pos, *w, is_origin);
        is_origin = false;
        pos = pos.wrapping_add(Unsigned18Bit::ONE);
    }
}

fn disassemble_word(loc: Unsigned18Bit, w: Unsigned36Bit, is_origin: bool) {
    if is_origin {
        print!("{:>06o}|", loc);
    } else {
        print!("{:7}", "");
    }
    let raw = Instruction::from(w);
    match SymbolicInstruction::try_from(&raw) {
        Ok(symbolic) => {
            print!("{:<20}", &symbolic.to_string());
        }
        Err(_) => {
            print!("{:<20}", "");
        }
    }
    println!("|{:>012o} {:>6o}", w, loc);
}

fn disassemble_chunk<R: Read>(input: &mut R, checksum: &mut Signed18Bit) -> Result<bool, Fail> {
    let first = read_splayed_words(input, 1, Some(checksum))?;
    let (chunk_size, origin) = match first.as_slice() {
        [only] => {
            let (len_rep, end) = split_halves(*only);
            let len = match Signed18Bit::ONE.checked_sub(len_rep.reinterpret_as_signed()) {
                Some(n) => {
                    if n.is_zero() {
                        Some(Unsigned18Bit::ZERO)
                    } else if n > Signed18Bit::ZERO {
                        Some(n.reinterpret_as_unsigned())
                    } else {
                        None
                    }
                }
                None => None,
            }
            .expect("overflow in block length");
            println!("** {}-word chunk ending at {}", len, end);
            let u_origin = end
                .checked_sub(len)
                .and_then(|n| n.checked_add(Unsigned18Bit::ONE))
                .expect("overflow in origin calculation");
            (u64::from(len) as usize, u_origin)
        }
        [] => return Err(Fail::ShortFile),
        _ => unreachable!(),
    };
    let block: Vec<Unsigned36Bit> = read_splayed_words(input, chunk_size, Some(checksum))?;
    let trailer: Vec<Unsigned36Bit> = read_splayed_words(input, 1, Some(checksum))?;
    let (_adj, next) = match trailer.as_slice() {
        [only] => split_halves(*only),
        [] => return Err(Fail::ShortFile),
        _ => unreachable!(),
    };
    disassemble_block(origin, &block);
    {
        let unsigned_checksum = checksum.reinterpret_as_unsigned();
        if unsigned_checksum.is_zero() {
            println!("** Checksum is valid: {:>06o}", unsigned_checksum);
        } else {
            println!(
                "** Checksum is not valid: {:>06o}, this tape cannot be loaded as-is",
                unsigned_checksum
            );
        }
    }
    if next == u18!(3) {
        Ok(true)
    } else if next == u18!(0o27) {
        println!("** This is the final block");
        Ok(false)
    } else {
        eprintln!("warning: block has unexpected next-address {:o}", next);
        Ok(false)
    }
}

fn check_header<R: Read>(input: &mut R) -> Result<(), Fail> {
    let expected_leader = reader_leader();
    let header = read_splayed_words(input, expected_leader.len(), None)?;
    for (pos, (want, got)) in expected_leader.iter().zip(header.iter()).enumerate() {
        if want != got {
            return Err(Fail::Generic(
		format!(
		    "File does not begin with the expected header; at position {} we expected {:>012o} but got {:>012o}",
		    pos, want, got)));
        }
    }
    println!("** reader leader is valid:");
    disassemble_block(Unsigned18Bit::from(3_u8), &header);
    println!("** end of reader leader");
    Ok(())
}

fn disassemble_file(input_file_name: &OsStr) -> Result<(), Fail> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| Fail::Generic(format!("failed to open input file: {}", e)))?;
    let mut reader = BufReader::new(input_file);
    check_header(&mut reader)?;
    let mut checksum: Signed18Bit = Signed18Bit::ZERO;
    loop {
        match disassemble_chunk(&mut reader, &mut checksum) {
            Ok(true) => (), // more data
            Ok(false) => {
                break;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }
    // The last block we read claimed it was the last.  Check that
    // there is no more data.
    let mut trailing_junk_count: usize = 0;
    let mut buf = [0; 1];
    loop {
        match reader.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => {
                for junk in buf {
                    eprintln!("trailing junk byte: {junk:o}");
                }
                trailing_junk_count = trailing_junk_count.saturating_add(n);
            }
            Err(e) => {
                return Err(Fail::ReadFailed(e.to_string()));
            }
        }
    }
    if trailing_junk_count > 0 {
        Err(Fail::Generic(
            "input file contains more data after what was apparently the last block".to_string(),
        ))
    } else {
        Ok(())
    }
}

fn disassemble() -> Result<(), Fail> {
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
            return Err(Fail::Generic(
		format!("failed to initialise tracing filter (perhaps there is a problem with environment variables): {}", e)));
        }
        Ok(layer) => layer,
    };

    tracing_subscriber::registry()
        .with(filter_layer)
        .with(fmt_layer)
        .init();

    let span = span!(Level::ERROR, "disassemble", input=?cli.input);
    let _enter = span.enter();
    disassemble_file(&cli.input)
}

fn main() {
    match disassemble() {
        Err(e) => {
            eprintln!("error: {}", e);
            std::process::exit(1);
        }
        Ok(()) => {
            std::process::exit(0);
        }
    }
}
