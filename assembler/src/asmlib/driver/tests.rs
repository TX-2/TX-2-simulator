use std::ops::{Range, Shl};

use super::super::ast::{
    ArithmeticExpression, Atom, HoldBit, InstructionFragment, LiteralValue, LocatedBlock,
    ManuscriptBlock, PunchCommand, SourceFile, Statement, TaggedProgramInstruction,
    UntaggedProgramInstruction,
};
use super::super::driver::symtab::LookupOperation;
use super::super::eval::{SymbolContext, SymbolLookup, SymbolValue};
use super::super::symbol::SymbolName;
use super::super::types::Span;
use super::assemble_pass1;
use super::{assemble_nonempty_valid_input, assemble_source};
use base::{
    charset::Script,
    prelude::{u18, u36, Address, Unsigned36Bit},
};

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    eprintln!("assemble_literal input: {input}");
    let (directive, symtab) = assemble_nonempty_valid_input(input);
    if symtab.has_definitions() {
        panic!("no symbol should have been generated");
    }
    let got = directive.blocks.as_slice();
    eprintln!("{got:#?}");
    match got {
        [LocatedBlock {
            origin: _,
            location: _,
            items,
        }] => {
            eprintln!("There are {} items", items.len());
            match items.as_slice() {
                [Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instruction:
                        UntaggedProgramInstruction {
                            holdbit: HoldBit::Unspecified,
                            parts,
                            span: _,
                        },
                })] => match parts.as_slice() {
                    [only_frag] => {
                        if only_frag == expected {
                            return;
                        }
                        panic!(
                            "expected single instruction {:?}\ngot {:?}",
                            &expected, &only_frag,
                        );
                    }
                    got => {
                        panic!("expected one instruction containing {expected:?}\ngot wrong number of fragments {got:?}");
                    }
                },
                _ => {
                    panic!(
                        "expected one instruction containing {expected:?}\ngot {} items {items:?}",
                        items.len()
                    );
                }
            }
        }
        got => {
            panic!("expected one instruction containing {expected:?}\ngot items {got:?}");
        }
    }
}

#[cfg(test)]
fn assemble_check_symbols(input: &str, target_address: Address, expected: &[(&str, SymbolValue)]) {
    use crate::eval::HereValue;

    let (_directive, mut symtab) = assemble_nonempty_valid_input(input);
    for (name, expected_value) in expected.iter() {
        let sym = SymbolName {
            canonical: name.to_string(),
        };
        let span = span(0..(name.len()));
        let context = SymbolContext::from((Script::Normal, span));
        let here = HereValue::Address(target_address);
        let mut op = LookupOperation::default();
        match symtab.lookup_with_op(&sym, span, &here, &context, &mut op) {
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

fn atom_to_fragment(atom: Atom) -> InstructionFragment {
    InstructionFragment::Arithmetic(ArithmeticExpression::from(atom))
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
                        parts: vec![atom_to_fragment(Atom::Literal(LiteralValue::from((
                            Span::from(0..2),
                            Script::Normal,
                            u36!(0o14)
                        ))))]
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
    if let [LocatedBlock {
        origin: _,
        location: _,
        items,
    }] = directive.blocks.as_slice()
    {
        if let [Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instruction:
                UntaggedProgramInstruction {
                    span: _,
                    holdbit: HoldBit::Unspecified,
                    parts: first_parts,
                },
        }), Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instruction:
                UntaggedProgramInstruction {
                    span: _,
                    holdbit: HoldBit::Unspecified,
                    parts: second_parts,
                },
        })] = items.as_slice()
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
        Address::ZERO,
        &[("FOO", SymbolValue::Final(u36!(0o210452_030106)))],
    );
}

#[test]
fn test_normal_hash_value() {
    let program =
        assemble_source(concat!("100| 2\n#\n",), Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));
    assert_eq!(program.chunks[0].words[0], u36!(2));
    assert_eq!(program.chunks[0].words[1], u36!(0o101));
}

#[test]
fn test_super_hash_value() {
    let program = assemble_source(concat!("1| @super_hash@\n",), Default::default())
        .expect("program is valid");
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o1)));
    assert_eq!(program.chunks[0].words[0], u36!(1).shl(30));
}

#[test]
fn test_sub_hash_value() {
    let program =
        assemble_source(concat!("1| @sub_hash@\n",), Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o1)));
    assert_eq!(program.chunks[0].words[0], u36!(1).shl(18));
}

#[test]
fn test_assign_hash_value() {
    // The point of this test is that it's allowed for # to be used in
    // an assignment, and it represents the address at which the
    // instruction is assembled.  So in our example here, the value of
    // FOO depends on the address at which it is being used.
    //
    // While the User Handbook isn't explicit about this point, we
    // know that M4 supported this, because the Sketchpad code uses
    // this, like so:
    //
    // SPLATTT=#-NLIST-MASBL,,#-NLIST+MASBL
    let program = assemble_source(
        concat!(
            "         FOO = #\n",
            "       START = 100\n",
            "START| @super_1@ FOO\n",
            "       @super_2@ FOO\n",
        ),
        Default::default(),
    )
    .expect("program is valid");
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));
    assert_eq!(program.chunks[0].words[0], u36!(0o10000000100));
    assert_eq!(program.chunks[0].words[1], u36!(0o20000000101));
}

#[test]
fn test_logical_or_on_constants() {
    let program1 = assemble_source("100| 4 ∨ 2\n", Default::default()).expect("program is valid");
    assert_eq!(program1.chunks[0].words[0], u36!(0o6));

    // Word assembly uses logical union.  The parse is different but
    // the value is the same.
    let program2 = assemble_source("100| 4 2\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o6));

    // Word assembly uses logical union, not add, so there is no carry.
    let program3 = assemble_source("100| 4 4\n", Default::default()).expect("program is valid");
    assert_eq!(program3.chunks[0].words[0], u36!(0o4));
}

#[test]
fn test_logical_and_on_constants() {
    let program1 = assemble_source("100| 6 ∧ 2\n", Default::default()).expect("program is valid");
    assert_eq!(program1.chunks[0].words[0], u36!(0o2));

    let program2 =
        assemble_source("100| 6 @and@ 4\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o4));
}

#[test]
fn test_addition_on_constants() {
    let program1 = assemble_source("100| 6 + 2\n", Default::default()).expect("program is valid");
    assert_eq!(program1.chunks[0].words[0], u36!(0o10));

    let program2 =
        assemble_source("100| 6 @add@ 2\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o10));
}

#[test]
fn test_subtraction_on_constants() {
    let program1 = assemble_source("100| 6 - 2\n", Default::default()).expect("program is valid");
    assert_eq!(program1.chunks[0].words[0], u36!(0o4));
}

#[test]
fn test_multiplication_on_constants() {
    let program1 =
        assemble_source("100| 6 @times@ 2\n", Default::default()).expect("program is valid");
    assert_eq!(program1.chunks[0].words[0], u36!(0o14));
    let program2 = assemble_source("100| 6×3\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o22));
}

#[test]
fn test_division_on_positive_constants() {
    // Positive division truncates towards zero.
    let program = assemble_source("100| 6 / 2\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o3));
    let program = assemble_source("100| 3 / 2\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o1));
    let program = assemble_source("100| 1 / 1\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o1));
    let program = assemble_source("100| 0 / 1\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o0));
}

#[test]
fn test_division_on_negative_constants() {
    let program = assemble_source(
        concat!("MINUSONE = 777777777776\n", "100| MINUSONE / 1\n"),
        Default::default(),
    )
    .expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o777_777_777_776));

    let program = assemble_source(
        concat!("MINUSONE = 777777777776\n", "100| 1 / MINUSONE\n"),
        Default::default(),
    )
    .expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o777_777_777_776));

    let program = assemble_source(
        concat!("MINUSONE = 777777777776\n", "100| MINUSONE / MINUSONE\n"),
        Default::default(),
    )
    .expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o1));
}

#[test]
fn test_division_overflow_on_constants() {
    // See the documentation for the opcode DIV (Users Handbook, page
    // 3-62) for a description of the rules around division by either
    // kind of zero.

    // Division by +0
    let program = assemble_source("100| 1 / 0\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o777_777_777_776)); // -1

    // Division by -0
    let program =
        assemble_source("100| 1 / 777777777777\n", Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o1)); // 1
}
