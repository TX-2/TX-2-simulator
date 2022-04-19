use crate::instruction::{Instruction, Opcode, OperandAddress, SymbolicInstruction};
use crate::onescomplement::unsigned::*;
use crate::types::Address;
use crate::{u18, u36, u5, u6};

/// Convert a bit designator (as described in the documentation for
/// the SKM opcode on page 3-34 of the User Handbook) into an
/// Unsigned6Bit field (suitable for use as the index portion of an
/// instruction word).
fn bit_index(q: u8, bitnum: u8) -> Unsigned6Bit {
    let quarter = match q {
        1 | 2 | 3 => q,
        4 => 0,
        _ => {
            panic!("invalid quarter number {}", q);
        }
    };
    if bitnum > 12 {
        panic!("invalid bit number {}", bitnum);
    }
    Unsigned6Bit::try_from(quarter << 4 | bitnum).unwrap()
}

#[test]
fn test_bit_index() {
    assert_eq!(
        bit_index(4, 12),
        Unsigned6Bit::try_from(12).expect("test data should be valid")
    );
}

/// Returns the standard reader leader.  The listing for this is given
/// on page 5-26 of the User Handbook.
///
/// This program is superficially similar to Program VI ("A Binary
/// Read-In Routine") in Lincoln Lab Memorandum 6M-5780 ("Some
/// Examples of TX-2 Programming"), but it is different in detail.
///
/// ## Disassembly
///
/// Here's a disassembly of the reader leader:
///
/// <pre>
/// Loc  Symbolic assembly
/// 00                   ** Used as a temporary for words read from tape
/// 01                   ** unused?
/// 02                   ** unused?
///
/// 03   ¹RSX₅₄ 5        ** set X₅₄=-5
/// 04  ³⁶JMP₅₄ 20       ** Call procedure to read first word into [0]
/// 05 h ²RSX₅₃ 0        ** Set X₅₃ = L([0])  ([0] is saved in E)
/// 06   ¹STE 11         ** Set R([11]) to the word we read from tape.
///
/// 07  ³⁶JMP₅₄ 17       ** Call procedure at 17 (clear metabit, read word)
/// 10 h  LDE   0        ** Load new word into E.
///                      ** R([11]) is the end address of the current
///                      ** block (this insruction is modified by the
///                      ** instruction at 06).
/// 11    STE₅₃ 34       ** Store new word at [X₅₃+34]
/// 12 h ¹JNX₅₃ 7        ** Loop to 7 when X₅₃<0. Postincrement X₅₃.
/// 13  ³⁶JMP₅₄ 20       ** Call procedure to read another word into [0]
/// 14 h  JPX₅₆ 377760   ** if X₅₆ > 0, restart tape loading
/// 15 h  JNX₅₆ 377760   ** if X₅₆ < 0, restart tape loading
/// 16  ¹⁴JPQ 27         ** Call user program (the instruction at 25 may have
///                      ** changed this address).
///
/// ** Read-word procedure (entry point 1, clears meta bit)
/// 17   ²MKZ₄.₁₂ 400011 ** Reset meta bit of [11]
/// ** Read-word procedure (entry point 2, meta bit unaffected)
/// ** On entry , X₅₄ is the return address.
/// 20   ¹RSX₅₇ 3        ** Set R(X₅₇)=R(3) which is 5.
/// 21 h  TSD 0          ** Read tape bits into [0].
/// 22  ³⁶JPX₅₇ 21       ** Loop (to TSD) when X₅₇>0 (i.e. do whole word)
/// 23   ¹AUX₅₆ 0        ** Add R[0] to X₅₆
/// 24 h ²AUX₅₆ 0        ** Add L[0] to X₅₆
/// 25   ¹STE 16         ** Set R[16] to E (which we loaded from [0]).
/// 26  ¹⁵BPQ₅₄ 0        ** Branch to X₅₄ (no offset) - in other words, return.
///
/// 27 ¹IOS₅₂ 20000    ** Disconnect PETR, load report word into E.
///                    ** This instruction is replaced by `JPQ AA` when
///                    ** a start address is used with ☛☛PUNCH.
/// </pre>
///
/// ## Input Format
///
/// I believe the input format expected by the standard reader leader
/// is:
///
/// <pre>
/// header word: len,,end
/// len bytes of body
/// trailer word: sum,,next
/// </pre>
///
/// All blocks start with `len,,end` where `len` is the negated value
/// of the actual length of the block in words (not including first
/// and last).  end is the address of the last word which should be
/// written by this block.
///
/// Neither the header word nor the trailer word is written into the
/// memory area identified by `end`.
///
/// The checksum calculation carried out in X₅₆ computes the unsigned
/// 18-bit total of left and right halves of all words in the block
/// (including the header and trailer words).  This checksum must come
/// out to 0, otherwise the reader leader will jump to 377760 to
/// restart the loading process (which will re-load the bin,
/// i.e. rewind the tape).
///
/// ## First, Middle and Last Blocks
///
/// All blocks except the last block should be created and are used in
/// the same way.  The last block is different from the others simply
/// because it has a different value of `next`.
///
/// The first block doesn't have to do anything in particular.  All
/// blocks except the last should end with `checksum,,3` in order to
/// make the reader leader read the next block.  The last block ends
/// with `checksum,,AA` where `AA` is the execution start address of
/// the user's program.
///
/// ## Minimal Example
///
/// I believe that the minimal tape content after the reader leader is
/// a block containing a single word.  This example shows such a block
/// loaded at address 0o20000:
///
/// <pre>
/// 0,,20000
/// 0
/// 740000,,20000
/// </pre>
///
/// Here the single word of the block (0) is loaded at 20000.  The
/// execution address is also 20000.  The instruction at 20000 is 0.
/// Since 0 is not a valid opcode, this program will fail. and the
/// TX-2 will raise the illegal instruction (OCSAL) alarm.
///
/// The checksum value 0o740000 ensures that the total of all four
/// halfwords is 0 (modulo 2^18).
///
/// ## Start Address
///
/// Notice that the disassembly above shows that address 27 contains
/// `¹IOS₅₂` 20000.  This is taken from the listing on page 5-26 of
/// the Users Handbook.  That apparently contraditcs the commentary on
/// page 6-23 of the same document, which states that the `IOS`
/// instruction is at location 26.  However, this difference is not
/// material.
///
/// If we follow the advice given on page 6-23 for the last word of a
/// block, we would set it to checksum,,26 meaning that the reader
/// leader at locaiton 16 will jump to location 26.  The instruction
/// at 26 (which is `¹⁵BPQ₅₄ 0`) will jump to the location in X₅₄.  That
/// will (I think) have been set to 27 by the previous execution of
/// `¹⁵BPQ₅₄ 0`.  So jump to location 26 has the effect of
/// jumping to location 27 but also sets X₅₄ (again) to 27.  This
/// seems indistinguishable from setting the R(last) to 27, because in
/// that case we begin execution at 27 with X₅₄ set to 27.
///
/// When the execution address of the last block is not either 26 or
/// 27, the user's program will need to disconnect the paper tape
/// reader if it doesn't require it.  This conclusion appears to
/// contradict the guidance on page 6-23. The apparent contradition
/// would be resolved if it were the case the M4 assembler adds a
/// special first block containing a jump at location 28, when the
/// `☛☛PUNCH` directive includes a start address.  This may in fact be
/// the case shown in the diagram on page 6-23.
pub fn reader_leader() -> Vec<Unsigned36Bit> {
    // The first 3 words of the leader are zero, and are used as
    // temporary storage.  These have no symbolic equivalent because
    // there is no opcode 0.
    let mut result: Vec<Unsigned36Bit> = vec![u36!(0), u36!(1), u36!(2)];

    fn build(b: SymbolicInstruction) -> Unsigned36Bit {
        Instruction::from(&b).bits()
    }

    const ZERO_ADDR: Address = Address::new(u18!(0));
    result.extend(
        [
            // These instructions are taken from the middle column of
            // page 5-26 of the Users Handbook.
            //
            // They are called by the boot code (the routine starting
            // at 0o377760, see listing in section 5-5.2 of the Users
            // Handbook).  The active sequence is 0o52, with X₅₂ =
            // 0o377763, X₅₃ = 0, X₅₄ = 0.
            //
            // ¹²³⁴⁵⁶⁷ ₀₁₂₃₃₄₅₆₇
            SymbolicInstruction {
                // 003: ¹RSX₅₄ 5   ** set X₅₄=-5
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Rsx,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o05))),
            },
            SymbolicInstruction {
                // 004: ³⁶JMP₅₄ 20
                held: false,
                configuration: u5!(0o36), // binary 011110
                /* Saves return address (which is 0o5) in X₅₄ and in
                       R(E) and last memory reference in L(E), dismiss (lower
                       the flag of sequence 52).  I believe that even though
                       we dismiss sequence 52, there is no other runnable
                       sequence, so execution continues.
                */
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o20))),
            },
            SymbolicInstruction {
                // 005: h²RSX₅₃ 0      ** Set X₅₃ = R([0])  ([0] is saved in E)
                /* R[0] was read (by the call to 0o20 just above) from
                 * the first word of the tape block. */
                held: true,
                configuration: u5!(2),
                opcode: Opcode::Rsx,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(ZERO_ADDR),
            },
            SymbolicInstruction {
                // 006: ¹STE 11        ** Set [11] to the word we read from tape.
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Ste,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o11))),
            },
            SymbolicInstruction {
                // 007: : ³⁶JMP₅₄ 17  ** Call procedure at 17
                /* Saves return address (which is 0o10) in X₅₄ and in
                       R(E) and last memory reference in L(E), dismiss
                       (lower the flag of sequence 52 - but this has
                       no effect since this already happened the first
                       time we executed the instruction at 004).  I
                       believe that even though we dismiss sequence
                       52, there is no other runnable sequence, so
                       execution continues.
                */
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o17))),
            },
            /* On return from the procedure at 0o17, [0] contains the
             * word we read. */
            SymbolicInstruction {
                // 010: hLDE 0        ** Load new word into E.
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Lde,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o00))),
            },
            SymbolicInstruction {
                // 011: STE₅₃ 34       ** Store new word at [X₅₃+34]
                /* X₅₃ was initialised to the RHS of the first word in
                 * the block and is incremented by the JNX instruction
                 * at the next location, 0o12.
                 */
                held: false,
                configuration: u5!(0),
                opcode: Opcode::Ste,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o34))),
            },
            SymbolicInstruction {
                // 012: h¹JNX₅₃ 7     ** Loop to 7 when X₅₃<0. Postincrement X₅₃.
                held: true,
                configuration: u5!(1),
                opcode: Opcode::Jnx,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o07))),
            },
            SymbolicInstruction {
                // 013: ³⁶JMP₅₄ 20     ** Call procedure to read another word into [0]
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o20))),
            },
            SymbolicInstruction {
                // 014: hJPX₅₆ 377760 ** if X₅₆ > 0, restart tape loading
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Jpx,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o377_760))),
            },
            SymbolicInstruction {
                // 015: hJNX₅₆ 377760 ** if X₅₆ < 0, restart tape loading
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Jnx,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o377760))),
            },
            SymbolicInstruction {
                // 016: ¹⁴JPQ 27
                //
                // We arrive at this location (from 15) if X₅₆ is zero
                // - that is, if the checksum is correct.
                //
                // Jump to register 27, which holds another jump
                // instruction; that jumps to the user's code entry
                // point.
                held: false,
                configuration: u5!(0o14),
                // ¹⁴JMP = JPQ, see page 3-31 of Users Handbook
                opcode: Opcode::Jmp,
                index: u6!(0o0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o27))),
            },
            SymbolicInstruction {
                // 017: ²MKZ₄.₁₂ 400011     ** Reset meta bit of [11]
                held: false,
                configuration: u5!(0o2),
                opcode: Opcode::Skm,       // ²SKM is Mkz (p 3-34) "make zero"
                index: bit_index(4, 0o12), // 4.12
                operand_address: OperandAddress::Deferred(Address::new(u18!(0o11))),
            },
            /* At 0o20 we have a procedure which loads a word from
             * tape, adds it to our running checksum and leaves the
             * word at [0]. */
            SymbolicInstruction {
                // 020: ¹RSX₅₇ 3     ** Set R(X₅₇)=R(3) which is 5.
                held: false,
                configuration: u5!(0o1),
                opcode: Opcode::Rsx,
                index: u6!(0o57),
                operand_address: OperandAddress::Direct(Address::new(u18!(3))),
            },
            SymbolicInstruction {
                // 021: hTSD 0        ** Read tape bits into [0].
                held: true,
                configuration: u5!(0), // ignored anyway in ASSEMBLY mode
                opcode: Opcode::Tsd,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 022: ³⁶JPX₅₇ 21     ** Loop (to TSD) when X₅₇>0 (i.e. do whole word)
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jpx,
                index: u6!(0o57),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o21))),
            },
            SymbolicInstruction {
                // 023: ¹AUX₅₆ 0        ** Add R[0] to X₅₆
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Aux,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 024: h²AUX₅₆ 0        ** Add L[0] to X₅₆
                //                       ** This also sets E to [0].
                held: true,
                configuration: u5!(2),
                opcode: Opcode::Aux,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 025: ¹STE 16         ** Set R[16] to E (which we loaded from [0]).
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Ste,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o16))),
            },
            SymbolicInstruction {
                // 026: ¹⁵BPQ₅₄ 0       ** Branch to X₅₄ (no offset)
                //                      ** This is return from procedure call,
                //                      ** e.g. from the call at 004.
                //                      ** Overwrites E with saved return point, mem ref
                held: false,
                configuration: u5!(0o15),
                opcode: Opcode::Jmp, // 0o05 is JMP (p 3-30); ¹⁵JMP = BPQ
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 027: ¹IOS₅₂ 20000     ** Disconnect PETR, load report word into E.
                held: false,
                configuration: u5!(1), // signals that PETR report word should be loaded into E
                opcode: Opcode::Ios,
                index: u6!(0o52),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o020_000))),
            },
        ]
        .into_iter()
        .map(build),
    );
    result
}

#[test]
fn test_reader_leader() {
    let leader = reader_leader();
    assert_eq!(leader.len(), 0o30);
    let expected: &[u64] = &[
        // These values are taken from the right-hand column of page
        // 5-26 of the Users Handbook.
        // Instruction (oct)  Position (oct)
        0o000_000_000_000, //  0
        0o000_000_000_001, //  1
        0o000_000_000_002, //  2
        0o011_154_000_005, //  3
        0o360_554_000_020, //  4
        0o421_153_000_000, //  5
        0o013_000_000_011, //  6
        0o360_554_000_017, //  7
        0o402_000_000_000, // 10
        0o003_053_000_034, // 11
        0o410_753_000_007, // 12
        0o360_554_000_020, // 13
        0o400_656_377_760, // 14
        0o400_756_377_760, // 15
        0o140_500_000_027, // 16
        0o021_712_400_011, // 17
        0o011_157_000_003, // 20
        0o405_700_000_000, // 21
        0o360_657_000_021, // 22
        0o011_056_000_000, // 23
        0o421_056_000_000, // 24
        0o013_000_000_016, // 25
        0o150_554_000_000, // 26
        0o010_452_020_000, // 27
    ];
    for (i, expected_value) in expected.iter().copied().map(u64::from).enumerate() {
        // 20
        assert_eq!(
            leader[i], expected_value,
            "Mismatch in reader leader at position {:#3o}: expected 0o{:012o}, got 0o{:012o}; got instruction disassembles to {:?}",
            i, expected_value, leader[i], &SymbolicInstruction::try_from(&Instruction::from(leader[i])),
        );
    }
}
