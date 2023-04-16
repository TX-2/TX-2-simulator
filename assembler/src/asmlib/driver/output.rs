use std::io::Write;
use std::path::Path;

use tracing::{event, span, Level};

use base::prelude::{
    join_halves, reader_leader, split_halves, u18, u5, u6, unsplay, Address, Instruction, Opcode,
    OperandAddress, Signed18Bit, SymbolicInstruction, Unsigned18Bit, Unsigned36Bit, Unsigned6Bit,
};

use super::super::types::AssemblerFailure;
use super::Binary;

fn write_data<W: Write>(
    writer: &mut W,
    output_file_name: &Path,
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
        filename: output_file_name.to_path_buf(),
        error: e,
    })
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
    address: Address,
    code: &[Unsigned36Bit],
    last: bool,
) -> Result<Vec<Unsigned36Bit>, AssemblerFailure> {
    if code.is_empty() {
        return Err(AssemblerFailure::BadTapeBlock(
            format!("tape block at {address:o} is empty but tape blocks are not allowed to be empty (the format does not support it)")
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
    let end: Unsigned18Bit = match Unsigned18Bit::from(address)
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
        "creating a tape block with origin={address:>06o}, len={len:o}, end={end:>06o}"
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
    let location = Address::from(Unsigned18Bit::from(0o27_u8));
    let code = vec![
        Instruction::from(&disconnect_tape).bits(),
        Instruction::from(&jump).bits(),
    ];
    create_tape_block(location, &code, !empty_program)
}

pub(crate) fn write_user_program<W: Write>(
    binary: &Binary,
    writer: &mut W,
    output_file_name: &Path,
) -> Result<(), AssemblerFailure> {
    let span = span!(Level::ERROR, "write binary program");
    let _enter = span.enter();

    // The boot code reads the paper tape in PETR mode 0o30106
    // (see base/src/memory.rs) which looks for an END MARK
    // (code 0o76, no seventh bit set).  But, our PETR device
    // emulation currently "invents" the END MARK (coinciding
    // with the beginnng of the tape file) so we don't need to
    // write it.
    write_data(writer, output_file_name, &reader_leader())?;
    for chunk in binary.chunks().iter() {
        if chunk.is_empty() {
            event!(Level::ERROR, "Will not write empty block at {:o}; the assembler should not have generated one; this is a bug.",
                   chunk.address,
            );
            continue;
        }
        let block = create_tape_block(chunk.address, &chunk.words, false)?;
        write_data(writer, output_file_name, &block)?;
    }

    // After the rest of the program is punched, we write the special
    // block for register 27.  This has to be last, becaause the
    // standard reader leader uses the "next" field of the header to
    // determine which is the last block.  When the "next" field
    // points at 0o27 instead of 0o3, that means this is the final
    // block.  WSo we have to emit this one last.
    write_data(
        writer,
        output_file_name,
        &create_begin_block(binary.entry_point(), binary.is_empty())?,
    )?;

    writer
        .flush()
        .map_err(|e| AssemblerFailure::IoErrorOnOutput {
            filename: output_file_name.to_owned(),
            error: e,
        })
}
