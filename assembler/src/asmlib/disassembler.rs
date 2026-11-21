use std::error::Error;
use std::ffi::OsStr;
use std::fmt::{self, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read};

use crate::reader_leader;
use base::prelude::*;

#[derive(Debug)]
pub enum DisassemblerFailure {
    ReadFailed(String),
    Generic(String),
    ShortFile,
}

impl Display for DisassemblerFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            DisassemblerFailure::Generic(message) | DisassemblerFailure::ReadFailed(message) => {
                f.write_str(message)
            }
            DisassemblerFailure::ShortFile => f.write_str("file ended unexpectedly"),
        }
    }
}

impl Error for DisassemblerFailure {}

fn update_sum(sum: Signed18Bit, word: Unsigned36Bit) -> Signed18Bit {
    let (left, right) = split_halves(word);
    sum.wrapping_add(right.reinterpret_as_signed())
        .wrapping_add(left.reinterpret_as_signed())
}

fn read_splayed_words<R: Read>(
    input: &mut R,
    count: usize,
    mut maybe_checksum: Option<&mut Signed18Bit>,
) -> Result<Vec<Unsigned36Bit>, DisassemblerFailure> {
    const SPLAY_SIZE: usize = 6;
    let mut result: Vec<Unsigned36Bit> = Vec::with_capacity(count);
    for _ in 0..count {
        let mut w = Unsigned36Bit::ZERO;
        let mut buf: [u8; SPLAY_SIZE] = [0; SPLAY_SIZE];
        match input.read(&mut buf) {
            Ok(0) => {
                return Err(DisassemblerFailure::ShortFile);
            }
            Ok(nbytes) => {
                if nbytes != SPLAY_SIZE {
                    return Err(DisassemblerFailure::Generic(
                        "input file length should be a multiple of 6 bytes".to_string(),
                    ));
                }
                for byte in buf.into_iter() {
                    let line: Unsigned6Bit = Unsigned6Bit::try_from(byte & 0o77).unwrap();
                    w = cycle_and_splay(w, line);
                }
                if let Some(ref mut checksum) = maybe_checksum {
                    **checksum = update_sum(**checksum, w);
                }
                result.push(w);
            }
            Err(e) => {
                return Err(DisassemblerFailure::ReadFailed(e.to_string()));
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
        print!("{loc:>06o}|");
    } else {
        print!("{:7}", "");
    }
    let raw = Instruction::from(w);
    match SymbolicInstruction::try_from(&raw) {
        Ok(symbolic) => {
            print!("{:<20}", symbolic.to_string());
        }
        Err(_) => {
            print!("{:<20}", "");
        }
    }
    let (left, right) = split_halves(w);
    println!("|{left:>06o} {right:>06o}|{loc:>6o}");
}

fn disassemble_chunk<R: Read>(
    input: &mut R,
    checksum: &mut Signed18Bit,
) -> Result<bool, DisassemblerFailure> {
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
            println!("** {len}-word chunk ending at {end}");
            let u_origin = end
                .checked_sub(len)
                .and_then(|n| n.checked_add(Unsigned18Bit::ONE))
                .expect("overflow in origin calculation");
            (u64::from(len) as usize, u_origin)
        }
        [] => return Err(DisassemblerFailure::ShortFile),
        _ => unreachable!(),
    };
    let block: Vec<Unsigned36Bit> = read_splayed_words(input, chunk_size, Some(checksum))?;
    let trailer: Vec<Unsigned36Bit> = read_splayed_words(input, 1, Some(checksum))?;
    let (_adj, next) = match trailer.as_slice() {
        [only] => split_halves(*only),
        [] => return Err(DisassemblerFailure::ShortFile),
        _ => unreachable!(),
    };
    disassemble_block(origin, &block);
    {
        let unsigned_checksum = checksum.reinterpret_as_unsigned();
        if unsigned_checksum.is_zero() {
            println!("** Checksum is valid: {unsigned_checksum:>06o}");
        } else {
            println!(
                "** Checksum is not valid: {unsigned_checksum:>06o}, this tape cannot be loaded as-is",
            );
        }
    }
    if next == u18!(3) {
        Ok(true)
    } else if next == u18!(0o27) {
        println!("** This is the final block");
        Ok(false)
    } else {
        eprintln!("warning: block has unexpected next-address {next:o}");
        Ok(false)
    }
}

fn check_header<R: Read>(input: &mut R) -> Result<(), DisassemblerFailure> {
    let expected_leader = reader_leader();
    let header = read_splayed_words(input, expected_leader.len(), None)?;
    for (pos, (want, got)) in expected_leader.iter().zip(header.iter()).enumerate() {
        if want != got {
            return Err(DisassemblerFailure::Generic(format!(
                "File does not begin with the expected header; at position {pos} we expected {want:>012o} but got {got:>012o}"
            )));
        }
    }
    println!("** reader leader is valid:");
    disassemble_block(Unsigned18Bit::from(3_u8), &header);
    println!("** end of reader leader");
    Ok(())
}

/// Disassemble input_file_name and print a source listing to stdout.
pub fn disassemble_file(input_file_name: &OsStr) -> Result<(), DisassemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| DisassemblerFailure::Generic(format!("failed to open input file: {e}")))?;
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
                return Err(DisassemblerFailure::ReadFailed(e.to_string()));
            }
        }
    }
    if trailing_junk_count > 0 {
        Err(DisassemblerFailure::Generic(
            "input file contains more data after what was apparently the last block".to_string(),
        ))
    } else {
        Ok(())
    }
}
