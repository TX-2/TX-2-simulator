use std::ops::Range;

use super::super::ast::{
    Block, Expression, HoldBit, InstructionFragment, LiteralValue, ManuscriptBlock, PunchCommand,
    SourceFile, Statement, TaggedProgramInstruction, UntaggedProgramInstruction,
};
use super::super::eval::{SymbolContext, SymbolLookup, SymbolValue};
use super::super::symbol::SymbolName;
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
            [TaggedProgramInstruction {
                tag: None,
                instruction:
                    UntaggedProgramInstruction {
                        holdbit: HoldBit::Unspecified,
                        parts,
                        span: _,
                    },
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

#[cfg(test)]
fn assemble_check_symbols(input: &str, expected: &[(&str, SymbolValue)]) {
    let (_directive, mut symtab) = assemble_nonempty_valid_input(input);
    for (name, expected_value) in expected.into_iter() {
        let sym = SymbolName {
            canonical: name.to_string(),
        };
        let span = span(0..(name.len()));
        let context = SymbolContext::from((Script::Normal, span));
        match symtab.lookup(&sym, span, &context) {
            Ok(got) => {
                if got != *expected_value {
                    panic!("incorrect value for symbol {name}; expected {expected_value:?}, got {got:?}");
                }
            }
            Err(e) => {
                panic!("unexpected error looking up value for symbol {name}: {e:?}");
            }
        }
    }
}

#[test]
fn test_assemble_pass1() {
    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let mut errors = Vec::new();
    let (source_file, _options) =
        assemble_pass1(input, &mut errors).expect("pass 1 should succeed");
    assert_eq!(errors.as_slice(), &[]);
    assert_eq!(
        source_file,
        Some(SourceFile {
            punch: Some(PunchCommand(Some(Address::from(u18!(0o26))))),
            blocks: vec![ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction: UntaggedProgramInstruction {
                        span: Span::from(0..2),
                        holdbit: HoldBit::Unspecified,
                        parts: vec![InstructionFragment {
                            value: Expression::Literal(LiteralValue::from((
                                Span::from(0..2),
                                Script::Normal,
                                u36!(0o14)
                            )))
                        }]
                    }
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
        if let [TaggedProgramInstruction {
            tag: None,
            instruction:
                UntaggedProgramInstruction {
                    span: _,
                    holdbit: HoldBit::Unspecified,
                    parts: first_parts,
                },
        }, TaggedProgramInstruction {
            tag: None,
            instruction:
                UntaggedProgramInstruction {
                    span: _,
                    holdbit: HoldBit::Unspecified,
                    parts: second_parts,
                },
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

#[test]
fn test_assignment_rhs_is_instruction() {
    // The RHS of an assignment can be "any 36-bit value" (see TX-2
    // Users Handbook, section 6-2.2, page 156 = 6-6).  Here we verify
    // that it can be an instruction.
    assemble_check_symbols(
        concat!(
            "FOO=²¹IOS₅₂ 30106  ** FROM PLUGBOARD A AT ADDRESS 377762\n",
            "** WE USE FOO TO MAKE SURE THE SYMBOL VALUE IS NEEDED\n",
            "** (AND HENCE IS RETAINED).\n",
            "FOO\n"
        ),
        &[("FOO", SymbolValue::Final(u36!(0o210452_030106)))],
    );
}
