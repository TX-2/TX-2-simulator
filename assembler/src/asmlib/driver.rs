use std::ffi::OsStr;
use std::fs::OpenOptions;
use std::io::{BufReader, BufWriter, Read, Write};

use tracing::{event, span, Level};

use crate::ast::*;
use crate::parser::{source_file, ErrorLocation};
use crate::state::Error;
use crate::symtab::*;
use crate::types::*;
use base::prelude::{
    join_halves, reader_leader, split_halves, u18, u5, u6, unsplay, Address, Instruction, Opcode,
    OperandAddress, Signed18Bit, SymbolicInstruction, Unsigned18Bit, Unsigned36Bit, Unsigned6Bit,
};
#[cfg(test)]
use base::u36;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct OutputOptions {
    // TODO: implement arguments of the LIST, PLIST, TYPE
    // metacommands.
    list: bool,
}

fn update_checksum_by_halfword(sum: Signed18Bit, halfword: Signed18Bit) -> Signed18Bit {
    sum.wrapping_add(halfword)
}

fn update_checksum(sum: Signed18Bit, word: Unsigned36Bit) -> Signed18Bit {
    let (l, r) = split_halves(word);
    update_checksum_by_halfword(
        update_checksum_by_halfword(l.reinterpret_as_signed(), sum),
        r.reinterpret_as_signed(),
    )
}

/// Create a block of data ready to be punched to tape such that the
/// standard reader leader can load it.
///
/// See reaaderleader.rs for documentation on the format of a block.
///
/// For the last block, the jump address is 0o26, which is the
/// location within the reader leader which arranges to start the
/// user's program.  For other blocks it is 3 (that is, we jump back
/// to the start of the reader leader in order to load the next
/// block).
fn create_tape_block(
    origin: Origin,
    code: &[Unsigned36Bit],
    last: bool,
) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
    if code.is_empty() {
        return Err(AssemblerFailure::BadTapeBlock(
            format!("tape block at {origin:o} is empty but tape blocks are not allowed to be empty (the format does not support it)")
        ));
    }
    let len: Unsigned18Bit = match Unsigned18Bit::try_from(code.len()) {
        Err(_) => {
            return Err(AssemblerFailure::BadTapeBlock(
                "block is too long for output format".to_string(),
            ));
        }
        Ok(len) => len,
    };
    let end: Unsigned18Bit = match Unsigned18Bit::from(origin)
        .checked_add(len)
        .and_then(|n| n.checked_sub(Unsigned18Bit::ONE))
    {
        None => {
            return Err(AssemblerFailure::BadTapeBlock(
                "end of block does not fit into physical memory".to_string(),
            ));
        }
        Some(end) => end,
    };
    event!(
        Level::DEBUG,
        "creating a tape block with origin={origin:>06o}, len={len:o}, end={end:>06o}"
    );
    let mut block = Vec::with_capacity(code.len().saturating_add(2usize));
    let encoded_len: Unsigned18Bit = match Signed18Bit::try_from(len) {
        Ok(n) => Signed18Bit::ONE.checked_sub(n),
        Err(_) => None,
    }
    .expect("overflow in length encoding")
    .reinterpret_as_unsigned();
    let mut checksum = Signed18Bit::ZERO;
    block.push(join_halves(encoded_len, end));
    block.extend(code);

    for w in block.iter() {
        checksum = update_checksum(checksum, *w);
    }
    let next: Unsigned18Bit = { if last { 0o27_u8 } else { 0o3_u8 }.into() };
    checksum = update_checksum_by_halfword(checksum, next.reinterpret_as_signed());
    let balance = Signed18Bit::ZERO.wrapping_sub(checksum);
    checksum = update_checksum_by_halfword(checksum, balance);
    block.push(join_halves(balance.reinterpret_as_unsigned(), next));
    assert_eq!(checksum, Signed18Bit::ZERO);
    Ok(block)
}

/// Assemble a single instruction to go into register 0o27,
/// immediately after the reader leader.  This instruction calls the
/// user's program.
fn create_begin_block(
    program_start: Option<Address>,
    empty_program: bool,
) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
    let disconnect_tape = SymbolicInstruction {
        // 027: ¹IOS₅₂ 20000     ** Disconnect PETR, load report word into E.
        held: false,
        configuration: u5!(1), // signals that PETR report word should be loaded into E
        opcode: Opcode::Ios,
        index: u6!(0o52),
        operand_address: OperandAddress::Direct(Address::new(u18!(0o020_000))),
    };
    let jump: SymbolicInstruction = if let Some(start) = program_start {
        // When there is a known start address `start` we emit a `JPQ
        // start` instruction into memory register 0o27.
        SymbolicInstruction {
            held: false,
            configuration: u5!(0o14), // JPQ
            opcode: Opcode::Jmp,
            index: Unsigned6Bit::ZERO,
            operand_address: OperandAddress::Direct(start),
        }
    } else {
        // Emit a JPD (jump, dismiss) instruction which loops back to
        // itself.  This puts the machine into the LIMBO state.
        SymbolicInstruction {
            held: false,
            configuration: u5!(0o20), // JPD
            opcode: Opcode::Jmp,
            index: Unsigned6Bit::ZERO,
            operand_address: OperandAddress::Direct(Address::from(u18!(0o27))),
        }
    };
    let origin = Origin(Address::from(Unsigned18Bit::from(0o27_u8)));
    let code = vec![
        Instruction::from(&disconnect_tape).bits(),
        Instruction::from(&jump).bits(),
    ];
    create_tape_block(origin, &code, !empty_program)
}

fn write_data<W: Write>(
    writer: &mut W,
    output_file_name: &OsStr,
    data: &[Unsigned36Bit],
) -> Result<(), AssemblerFailure> {
    let mut inner = || -> Result<(), std::io::Error> {
        const OUTPUT_CHUNK_SIZE: usize = 1024;
        for chunk in data.chunks(OUTPUT_CHUNK_SIZE) {
            let mut buf: Vec<u8> = Vec::with_capacity(chunk.len() * 6);
            for word in chunk {
                let unsplayed: [Unsigned6Bit; 6] = unsplay(*word);
                buf.extend(unsplayed.into_iter().map(|u| u8::from(u) | 1 << 7));
            }
            writer.write_all(&buf)?;
        }
        Ok(())
    };
    inner().map_err(|e| AssemblerFailure::IoErrorOnOutput {
        filename: output_file_name.to_owned(),
        error: e,
    })
}

fn assemble_pass1(
    source_file_body: &str,
    symbols: &mut SymbolTable,
    errors: &mut Vec<Error>,
) -> Result<(Directive, OutputOptions), AssemblerFailure> {
    let span = span!(Level::ERROR, "assembly pass 1");
    let _enter = span.enter();
    let options = OutputOptions {
        // Because we don't parse the LIST etc. metacommands yet, we
        // simply hard-code the list option so that the symbol table isn't
        // unused.
        list: true,
    };
    let manuscript: Vec<ManuscriptBlock> = source_file(source_file_body, symbols, errors)?;
    let mut directive: Directive = Directive::new();
    let mut saw_punch: bool = false;
    for mblock in manuscript {
        let effective_origin = match mblock.origin {
            None => {
                let address = Origin::default();
                event!(
                    Level::DEBUG,
                    "Locating a block at default address {:o}",
                    address
                );
                address
            }
            Some(address) => {
                event!(
                    Level::DEBUG,
                    "Locating a block at specified address {:o}",
                    address
                );
                address
            }
        };
        let mut block = Block {
            origin: effective_origin,
            items: Vec::new(),
        };
        for manuscript_item in mblock.items {
            match manuscript_item {
                ManuscriptItem::Instruction(inst) => {
                    block.push(inst);
                }
                ManuscriptItem::MetaCommand(ManuscriptMetaCommand::Punch(address)) => {
                    saw_punch = true;
                    match address {
                        Some(a) => {
                            event!(Level::INFO, "program entry point was specified as {:o}", a);
                            directive.set_entry_point(a);
                        }
                        None => {
                            event!(Level::INFO, "program entry point was not specified");
                        }
                    }
                    // Because the PUNCH instruction causes the assembler
                    // output to be punched to tape, this effectively
                    // marks the end of the input.  On the real M4
                    // assembler it is likely possible for there to be
                    // more manuscript after the PUNCH metacommand, and
                    // for this to generate a fresh reader leader and so
                    // on.  But this is not supported here.  The reason we
                    // don't support it is that we'd need to know the
                    // answers to a lot of quesrtions we don't have
                    // answers for right now.  For example, should the
                    // existing program be cleared?  Should the symbol
                    // table be cleared?
                    break;
                }
                ManuscriptItem::MetaCommand(_) => (),
            }
        }
        directive.push(block);
    }
    if !saw_punch {
        event!(
            Level::WARN,
            "No PUNCH directive was given, program has no start address"
        );
    }
    // TODO: implement the SAVE metacommand.
    // TODO: implement the READ metacommand.
    // TODO: implement the TAPE metacommand.
    // TODO: implement the CORE metacommand.
    // TODO: implement the ERRORS metacommand.
    Ok((directive, options))
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let mut errors: Vec<Error> = Vec::new();
    // There is no origin specified in the input code, so we get the
    // default origin, octal 200000 (see section 6-2.5 of the Users
    // Handbook).  The origin of the code is not the same as the code
    // entry point (which is what is specified in the PUNCH
    // metacommand).
    let expected_directive_entry_point = Address::new(u18!(0o26));
    let expected_block = Block {
        origin: Origin::default(),
        items: vec![ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: vec![InstructionFragment {
                value: Expression::Literal(LiteralValue::from((Elevation::Normal, u36!(0o14)))),
            }],
        }],
    };

    let mut symbols = SymbolTable::new();
    let (directive, _options) =
        assemble_pass1(input, &mut symbols, &mut errors).expect("pass 1 should succeed");
    assert_eq!(
        Some(expected_directive_entry_point),
        directive.entry_point()
    );
    match directive.blocks.as_slice() {
        [block] => {
            assert_eq!(block, &expected_block);
        }
        [] => {
            panic!("expected a single block, got none");
        }
        _ => {
            panic!(
                "expected a single block at {:o}, got {:?}",
                Origin::default(),
                directive
            );
        }
    }
}

fn assemble_pass2(directive: &Directive) -> Vec<(Origin, Vec<Unsigned36Bit>)> {
    let span = span!(Level::ERROR, "assembly pass 2");
    let _enter = span.enter();
    let mut result: Vec<(Origin, Vec<Unsigned36Bit>)> = Vec::new();
    for block in directive.blocks.iter() {
        let words: Vec<Unsigned36Bit> = block.items.iter().map(|inst| inst.value()).collect();
        result.push((block.origin, words));
    }
    result
}

pub fn assemble_file(
    input_file_name: &OsStr,
    output_file_name: &OsStr,
) -> Result<(), AssemblerFailure> {
    let input_file = OpenOptions::new()
        .read(true)
        .open(input_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnInput {
            filename: input_file_name.to_owned(),
            error: e,
            line_number: None,
        })?;

    let mut symbols = SymbolTable::new();
    let mut source_file_body: String = String::new();
    let (directive, options) =
        match BufReader::new(input_file).read_to_string(&mut source_file_body) {
            Err(e) => {
                return Err(AssemblerFailure::IoErrorOnInput {
                    filename: input_file_name.to_owned(),
                    error: e,
                    line_number: None,
                })
            }
            Ok(_) => {
                let mut errors = Vec::new();
                let directive = assemble_pass1(&source_file_body, &mut symbols, &mut errors)?;
                match errors.as_slice() {
                    [first, ..] => {
                        for e in errors.iter() {
                            eprintln!("{}", e);
                        }
                        let location: &ErrorLocation = &first.0;
                        let msg = first.1.as_str();
                        return Err(AssemblerFailure::SyntaxError {
                            line: location.line,
                            column: location.column,
                            msg: msg.to_string(),
                        });
                    }
                    [] => directive,
                }
            }
        };
    event!(
        Level::INFO,
        "assembly pass1 generated {} instructions",
        directive.instruction_count()
    );

    // Now we do pass 2.
    if options.list {
        symbols
            .list()
            .map_err(|e| AssemblerFailure::IoErrorOnStdout { error: e })?;
    }

    let user_program: Vec<(Origin, Vec<Unsigned36Bit>)> = assemble_pass2(&directive);

    // The Users Guide explains on page 6-23 how the punched binary
    // is created (and read back in).
    let output_file = OpenOptions::new()
        .create(true)
        .write(true)
        .open(output_file_name)
        .map_err(|e| AssemblerFailure::IoErrorOnOutput {
            filename: output_file_name.to_owned(),
            error: e,
        })?;
    let mut writer = BufWriter::new(output_file);
    // The boot code reads the paper tape in PETR mode 0o30106
    // (see base/src/memory.rs) which looks for an END MARK
    // (code 0o76, no seventh bit set).  But, our PETR device
    // emulation currently "invents" the END MARK (coinciding
    // with the beginnng of the tape file) so we don't need to
    // write it.
    write_data(&mut writer, output_file_name, &reader_leader())?;
    for (origin, code) in &user_program {
        if code.is_empty() {
            event!(Level::ERROR, "Will not write empty block at {origin:o}; the assembler should not have generated one; this is a bug.");
            continue;
        }
        let block = create_tape_block(*origin, code, false)?;
        write_data(&mut writer, output_file_name, &block)?;
    }

    // After the rest of the program is punched, we write the special
    // block for register 27.  This has to be last, becaause the
    // standard reader leader uses the "next" field of the header to
    // determine which is the last block.  When the "next" field
    // points at 0o27 instead of 0o3, that means this is the final
    // block.  WSo we have to emit this one last.
    write_data(
        &mut writer,
        output_file_name,
        &create_begin_block(directive.entry_point(), user_program.is_empty())?,
    )?;

    writer
        .flush()
        .map_err(|e| AssemblerFailure::IoErrorOnOutput {
            filename: output_file_name.to_owned(),
            error: e,
        })
}
