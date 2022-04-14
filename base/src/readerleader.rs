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
            SymbolicInstruction {
                // 003
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Rsx,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(5))),
            },
            SymbolicInstruction {
                // 004
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o20))),
            },
            SymbolicInstruction {
                // 005
                held: true,
                configuration: u5!(2),
                opcode: Opcode::Rsx,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(ZERO_ADDR),
            },
            SymbolicInstruction {
                // 006
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Ste,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o11))),
            },
            SymbolicInstruction {
                // 007
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o17))),
            },
            SymbolicInstruction {
                // 010
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Lde,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 011
                held: false,
                configuration: u5!(0),
                opcode: Opcode::Ste,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o34))),
            },
            SymbolicInstruction {
                // 012
                held: true,
                configuration: u5!(1),
                opcode: Opcode::Jnx,
                index: u6!(0o53),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o7))),
            },
            SymbolicInstruction {
                // 013
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jmp,
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o20))),
            },
            SymbolicInstruction {
                // 014
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Jpx,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o377_760))),
            },
            SymbolicInstruction {
                // 015
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Jnx,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o377760))),
            },
            SymbolicInstruction {
                // 016
                // assembles to 0o140_500_000_0027
                held: false,
                configuration: u5!(0o14),
                // ¹⁴JMP = JPQ, see page 3-31 of Users Handbook
                opcode: Opcode::Jmp,
                index: u6!(0o0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o27))),
            },
            SymbolicInstruction {
                // 017
                // assembles to 0o021_712_400_011
                held: false,
                configuration: u5!(0o2),
                opcode: Opcode::Skm,       // ²SKM is Mkz (p 3-34) "make zero"
                index: bit_index(4, 0o12), // 4.12
                operand_address: OperandAddress::Deferred(Address::new(u18!(0o11))),
            },
            SymbolicInstruction {
                // 020
                held: false,
                configuration: u5!(0o1),
                opcode: Opcode::Rsx,
                index: u6!(0o57),
                operand_address: OperandAddress::Direct(Address::new(u18!(3))),
            },
            SymbolicInstruction {
                // 021
                held: true,
                configuration: u5!(0),
                opcode: Opcode::Tsd,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 022
                held: false,
                configuration: u5!(0o36),
                opcode: Opcode::Jpx,
                index: u6!(0o57),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o21))),
            },
            SymbolicInstruction {
                // 023
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Aux,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 024
                held: true,
                configuration: u5!(2),
                opcode: Opcode::Aux,
                index: u6!(0o56),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 025
                held: false,
                configuration: u5!(1),
                opcode: Opcode::Ste,
                index: u6!(0),
                operand_address: OperandAddress::Direct(Address::new(u18!(0o16))),
            },
            SymbolicInstruction {
                // 026
                // assembles to 0o150_554_000_000
                held: false,
                configuration: u5!(0o15),
                opcode: Opcode::Jmp, // 0o05 is JMP (p 3-30); ¹⁵JMP = BPQ
                index: u6!(0o54),
                operand_address: OperandAddress::Direct(Address::new(u18!(0))),
            },
            SymbolicInstruction {
                // 027
                held: false,
                configuration: u5!(1),
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
