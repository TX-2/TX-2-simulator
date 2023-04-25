use base::prelude::{u18, u36, Address, Unsigned36Bit};

use super::super::ast::{
    Block, Elevation, Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock,
    ProgramInstruction, PunchCommand, SourceFile, Statement,
};
use super::assemble_nonempty_valid_input;
use super::assemble_pass1;

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    let (directive, symtab) = assemble_nonempty_valid_input(input);
    if !symtab.is_empty() {
        panic!("no symbol should have been generated");
    }
    match directive.blocks.as_slice() {
        [Block { origin: _, items }] => match items.as_slice() {
            [ProgramInstruction {
                tag: None,
                holdbit: HoldBit::Unspecified,
                parts,
            }] => match parts.as_slice() {
                [only_frag] => {
                    if only_frag == expected {
                        return;
                    }
                }
                _ => (), // fall through to panic.
            },
            _ => (), // fall through to panic.
        },
        _ => (), // fall through to panic.
    }
    panic!(
        "expected one instruction containing {:?}, got {:?}",
        &expected, &directive,
    );
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let mut errors = Vec::new();
    let (source_file, _options) =
        assemble_pass1(input, &mut errors).expect("pass 1 should succeed");

    assert_eq!(
        source_file,
        Some(SourceFile {
            punch: Some(PunchCommand(Some(Address::from(u18!(0o26))))),
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(ProgramInstruction {
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment {
                        value: Expression::Literal(LiteralValue::from((
                            Elevation::Normal,
                            u36!(0o14)
                        )))
                    }]
                })]
            }]
        })
    );
}

#[test]
fn test_metacommand_dec_changes_default_base() {
    const INPUT: &str = concat!("10\n", "☛☛DECIMAL\n", "10  ** Ten\n");
    let (directive, _) = assemble_nonempty_valid_input(INPUT);
    if let [Block { origin: _, items }] = directive.blocks.as_slice() {
        if let [ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: first_parts,
        }, ProgramInstruction {
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: second_parts,
        }] = items.as_slice()
        {
            assert_eq!(
                &first_parts.as_slice(),
                &[InstructionFragment::from((
                    Elevation::Normal,
                    Unsigned36Bit::from(0o10_u32),
                ))],
            );
            assert_eq!(
                &second_parts.as_slice(),
                &[InstructionFragment::from((
                    Elevation::Normal,
                    Unsigned36Bit::from(0o12_u32),
                ))],
            );
            return;
        }
    }
    panic!(
        "expected two items with value 10 octal and 12 octal, got {:?}",
        &directive,
    );
}

#[test]
fn test_assemble_octal_superscript_literal() {
    assemble_literal(
        "⁺³⁶\n", // 36, superscript
        &InstructionFragment::from((Elevation::Superscript, Unsigned36Bit::from(0o36_u32))),
    );
}

#[test]
fn test_assemble_octal_subscript_literal() {
    assemble_literal(
        "₁₃\n", // without sign
        &InstructionFragment::from((Elevation::Subscript, Unsigned36Bit::from(0o13_u32))),
    );
    assemble_literal(
        "₊₁₃\n", // with optional + sign
        &InstructionFragment::from((Elevation::Subscript, Unsigned36Bit::from(0o13_u32))),
    );
}
