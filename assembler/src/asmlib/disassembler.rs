use std::error::Error;
use std::ffi::OsStr;
use std::fmt::{self, Display, Formatter};
use std::fs::OpenOptions;
use std::io::{BufReader, Read};

use crate::reader_leader;
use base::prelude::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OutputKind {
    DisassembleAsComment,
    DisassembleAsSource,
}

#[derive(Debug)]
pub enum DisassemblerFailure {
    ReadFailed(String),
    OutputFailed(std::io::Error),
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
            DisassemblerFailure::OutputFailed(inner) => {
                write!(f, "failed to write output: {inner}") // good luck!
            }
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
                for byte in buf {
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

fn disassemble_block<W: std::io::Write>(
    mut pos: Unsigned18Bit,
    block: &[Unsigned36Bit],
    how: OutputKind,
    output: &mut W,
) -> Result<(), std::io::Error> {
    let mut is_origin: bool = true;
    for w in block {
        disassemble_word(pos, *w, is_origin, how, output)?;
        is_origin = false;
        pos = pos.wrapping_add(Unsigned18Bit::ONE);
    }
    Ok(())
}

fn disassemble_word<W: std::io::Write>(
    loc: Unsigned18Bit,
    w: Unsigned36Bit,
    is_origin: bool,
    how: OutputKind,
    output: &mut W,
) -> Result<(), std::io::Error> {
    match how {
        OutputKind::DisassembleAsComment => {
            write!(output, "** ")?;
        }
        OutputKind::DisassembleAsSource => {
            // Emit 3 spaces to keep everything  lined up.
            write!(output, "   ")?;
        }
    }
    if is_origin {
        write!(output, "{loc:>06o}|")?;
    } else {
        write!(output, "{:7}", "")?;
    }
    let raw = Instruction::from(w);
    match SymbolicInstruction::try_from(&raw) {
        Ok(symbolic) => {
            let symbolic_as_string = symbolic.to_string();
            write!(output, "{symbolic_as_string:<20}")?;
        }
        Err(_) => {
            // Cannot disassemble into a symbolic form, print its
            // value.
            let _ = write!(output, "{w:<20o}");
        }
    }
    let (left, right) = split_halves(w);
    writeln!(output, "** |{left:>06o} {right:>06o}|{loc:>6o}")
}

fn report_on_checksum<W: std::io::Write, V: std::io::Write>(
    checksum: Signed18Bit,
    output: &mut W,
    warning_output: &mut V,
) -> Result<(), std::io::Error> {
    let unsigned_checksum = checksum.reinterpret_as_unsigned();
    if unsigned_checksum.is_zero() {
        writeln!(output, "** Checksum is valid: {unsigned_checksum:>06o}")
    } else {
        writeln!(
            warning_output,
            "** Checksum is not valid: {unsigned_checksum:>06o}, this tape cannot be loaded as-is",
        )
    }
}

fn read_chunk<R: Read, W: std::io::Write>(
    input: &mut R,
    checksum: &mut Signed18Bit,
    output: &mut W,
) -> Result<(Unsigned18Bit, Vec<Unsigned36Bit>, Unsigned18Bit), DisassemblerFailure> {
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
            writeln!(output, "** {len}-word chunk ending at {end}")
                .map_err(DisassemblerFailure::OutputFailed)?;
            let u_origin = end
                .checked_sub(len)
                .and_then(|n| n.checked_add(Unsigned18Bit::ONE))
                .expect("overflow in origin calculation");
            let chunk_size: usize = usize::from(len);
            (chunk_size, u_origin)
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
    Ok((origin, block, next))
}

fn is_final_block<W: std::io::Write, V: std::io::Write>(
    next: Unsigned18Bit,
    output: &mut W,
    warning_output: &mut V,
) -> Result<bool, std::io::Error> {
    if next == u18!(3) {
        Ok(true)
    } else if next == u18!(0o27) {
        writeln!(output, "** This is the final block")?;
        Ok(false)
    } else {
        writeln!(
            warning_output,
            "warning: block has unexpected next-address {next:o}"
        )?;
        Ok(false)
    }
}

fn disassemble_chunk<R: Read, W: std::io::Write, V: std::io::Write>(
    input: &mut R,
    checksum: &mut Signed18Bit,
    how: OutputKind,
    output: &mut W,
    warning_output: &mut V,
) -> Result<bool, DisassemblerFailure> {
    let (origin, block, next) = read_chunk(input, checksum, output)?;

    disassemble_block(origin, &block, how, output)
        .and_then(|()| report_on_checksum(*checksum, output, warning_output))
        .and_then(|()| is_final_block(next, output, warning_output))
        .map_err(DisassemblerFailure::OutputFailed)
}

fn check_header<R: Read, W: std::io::Write>(
    input: &mut R,
    leader_handling: OutputKind,
    output: &mut W,
) -> Result<(), DisassemblerFailure> {
    let expected_leader = reader_leader();
    let header = read_splayed_words(input, expected_leader.len(), None)?;
    for (pos, (want, got)) in expected_leader.iter().zip(header.iter()).enumerate() {
        if want != got {
            return Err(DisassemblerFailure::Generic(format!(
                "File does not begin with the expected header; at position {pos} we expected {want:>012o} but got {got:>012o}"
            )));
        }
    }
    writeln!(output, "** reader leader is valid:")
        .and_then(|()| {
            disassemble_block(Unsigned18Bit::from(3_u8), &header, leader_handling, output)
        })
        .and_then(|()| writeln!(output, "** end of reader leader"))
        .map_err(DisassemblerFailure::OutputFailed)?;
    Ok(())
}

fn check_start_instruction<R: Read, W: std::io::Write, V: std::io::Write>(
    input: &mut R,
    handling: OutputKind,
    checksum: &mut Signed18Bit,
    output: &mut W,
    warning_output: &mut V,
) -> Result<Option<Unsigned18Bit>, DisassemblerFailure> {
    let mut program_start_address: Option<Unsigned18Bit> = None;

    let (origin, block, _) = read_chunk(input, checksum, output)?;
    let mut is_standard: bool = true;

    // The first of these two words should be ¹IOS₅₂ 20000        ** |010452 020000|
    match block.as_slice() {
        &[first_word, second_word] if first_word == u36!(0o010_452_020_000) => {
            // If the program has a start address, the next word would be
            // ¹⁴JPQ <N> where <N> is the start address.  Otherwise it is
            // ²⁰JPD 27.
            let (operation, operand) = split_halves(second_word);
            if operation == u18!(0o140_500 /* ¹⁴JPQ */) {
                // There is a start address.
                program_start_address = Some(operand);
            }
        }
        _ => {
            writeln!(
                warning_output,
                "This program has a non-startard starup jump instruction at {origin:06o}"
            )
            .and_then(|()| {
                writeln!(
                    output,
                    "** The boot instructions at register 0o27 have unexpected values:"
                )
            })
            .map_err(DisassemblerFailure::OutputFailed)?;
            is_standard = false;
        }
    }

    if is_standard {
        writeln!(output, "** Standard startup jump block at {origin:06o}:")
    } else {
        writeln!(
            output,
            "** Startup jump block at {origin:06o} is non-standard:"
        )
    }
    .and_then(|()| disassemble_block(origin, &block, handling, output))
    .map_err(DisassemblerFailure::OutputFailed)?;

    Ok(program_start_address)
}

/// Disassemble `input_file_name` and print a source listing to stdout.
///
/// # Errors
///
/// Fail if we were unable to open or read the input, to write output,
/// if the input file is too short or otherwise invalid.
pub fn disassemble_file<W: std::io::Write, V: std::io::Write>(
    input_file_name: &OsStr,
    disassemble_leader: bool,
    output: &mut W,
    warning_output: &mut V,
) -> Result<(), DisassemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| DisassemblerFailure::Generic(format!("failed to open input file: {e}")))?;
    let mut reader = BufReader::new(input_file);

    let leader_output: OutputKind = if disassemble_leader {
        OutputKind::DisassembleAsSource
    } else {
        OutputKind::DisassembleAsComment
    };

    check_header(&mut reader, leader_output, output)?;
    let mut checksum: Signed18Bit = Signed18Bit::ZERO;

    let program_start_address = check_start_instruction(
        &mut reader,
        leader_output,
        &mut checksum,
        output,
        warning_output,
    )?;

    loop {
        // The first chunk after the reader leader is also emitted by
        // the assembler (into registers 0o27 and 0o30) and is not
        // part of the user's source file input.
        match disassemble_chunk(
            &mut reader,
            &mut checksum,
            OutputKind::DisassembleAsSource,
            output,
            warning_output,
        ) {
            Ok(true) => (), // more data
            Ok(false) => {
                break;
            }
            Err(e) => {
                return Err(e);
            }
        }
    }

    // Emit a PUNCH metacommand if the program had a start address.
    if let Some(program_start_address) = program_start_address {
        writeln!(output, "☛☛PUNCH {program_start_address:o}")
    } else {
        writeln!(output, "☛☛PUNCH ** There is no start address")
    }
    .map_err(DisassemblerFailure::OutputFailed)?;

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
