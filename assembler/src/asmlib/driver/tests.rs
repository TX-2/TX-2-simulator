use std::ops::Range;

use super::super::ast::{
    Block, Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock,
    ProgramInstruction, PunchCommand, SourceFile, Statement,
};
use super::super::types::Span;
use super::assemble_nonempty_valid_input;
use super::assemble_pass1;
use base::{
    charset::Script,
    prelude::{u18, u36, Address, Unsigned36Bit},
};

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    let (directive, symtab) = assemble_nonempty_valid_input(input);
    if !symtab.is_empty() {
        panic!("no symbol should have been generated");
    }
    match directive.blocks.as_slice() {
        [Block {
            origin: _,
            location: _,
            items,
        }] => match items.as_slice() {
            [ProgramInstruction {
                span: _,
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
                    span: Span::from(0..2),
                    tag: None,
                    holdbit: HoldBit::Unspecified,
                    parts: vec![InstructionFragment {
                        value: Expression::Literal(LiteralValue::from((
                            Span::from(0..2),
                            Script::Normal,
                            u36!(0o14)
                        )))
                    }]
                })]
            }]
        })
    );
}

fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

#[test]
fn test_metacommand_dec_changes_default_base() {
    const INPUT: &str = concat!("10\n", "☛☛DECIMAL\n", "10  ** Ten\n");
    let (directive, _) = assemble_nonempty_valid_input(INPUT);
    if let [Block {
        origin: _,
        location: _,
        items,
    }] = directive.blocks.as_slice()
    {
        if let [ProgramInstruction {
            span: _,
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: first_parts,
        }, ProgramInstruction {
            span: _,
            tag: None,
            holdbit: HoldBit::Unspecified,
            parts: second_parts,
        }] = items.as_slice()
        {
            assert_eq!(
                &first_parts.as_slice(),
                &[InstructionFragment::from((
                    Span::from(0..2usize),
                    Script::Normal,
                    Unsigned36Bit::from(0o10_u32),
                ))],
            );
            assert_eq!(
                &second_parts.as_slice(),
                &[InstructionFragment::from((
                    span(17..19),
                    Script::Normal,
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
        &InstructionFragment::from((span(0..8), Script::Super, Unsigned36Bit::from(0o36_u32))),
    );
}

#[test]
fn test_assemble_octal_subscript_literal_nosign() {
    assemble_literal(
        "₁₃\n", // without sign
        &InstructionFragment::from((span(0..6), Script::Sub, Unsigned36Bit::from(0o13_u32))),
    );
}

#[test]
fn test_assemble_octal_subscript_literal_plussign() {
    assemble_literal(
        "₊₁₃\n", // with optional + sign
        &InstructionFragment::from((span(0..9), Script::Sub, Unsigned36Bit::from(0o13_u32))),
    );
}
