use std::{
    collections::BTreeMap,
    ops::{Range, Shl},
};

use super::super::ast::{
    ArithmeticExpression, Atom, CommaDelimitedInstruction, ConfigValue, HoldBit,
    InstructionFragment, LiteralValue, LocatedBlock, ManuscriptBlock, PunchCommand, SourceFile,
    Statement, TaggedProgramInstruction, UntaggedProgramInstruction,
};
use super::super::eval::{make_empty_rc_block_for_test, SymbolLookup, SymbolValue};
use super::super::span::*;
use super::super::symbol::{SymbolContext, SymbolName};
use super::super::symtab::LookupOperation;
use super::super::types::BlockIdentifier;
use super::assemble_pass1;
use super::{assemble_nonempty_valid_input, assemble_source};
use base::{
    charset::Script,
    prelude::{u18, u36, Address, Unsigned18Bit, Unsigned36Bit},
};

#[cfg(test)]
fn assemble_literal(input: &str, expected: &InstructionFragment) {
    eprintln!("assemble_literal input: {input}");
    let (directive, symtab) = assemble_nonempty_valid_input(input);
    if symtab.has_definitions() {
        panic!("no symbol should have been generated");
    }
    let gotvec: Vec<LocatedBlock> = directive.blocks.into_values().collect();
    let got = gotvec.as_slice();
    eprintln!("{got:#?}");
    match got {
        [LocatedBlock {
            location: _,
            statements,
        }] => {
            eprintln!("There are {} items", statements.len());
            match statements.as_slice() {
                [] => {
                    panic!("no statement was assembled");
                }
                [Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instructions,
                })] => match instructions.as_slice() {
                    [] => {
                        panic!("no instruction was assembled");
                    }
                    [CommaDelimitedInstruction {
                        leading_commas,
                        instruction:
                            UntaggedProgramInstruction {
                                holdbit: HoldBit::Unspecified,
                                inst: only_frag,
                                span: _,
                            },
                        trailing_commas,
                    }] => {
                        assert!(leading_commas.is_none());
                        assert!(trailing_commas.is_none());
                        if only_frag == expected {
                            return;
                        }
                        panic!(
                            "expected single instruction {:?}\ngot {:?}",
                            &expected, &only_frag,
                        );
                    }
                    _ => {
                        panic!(
                                "expected one instruction containing {expected:?}\ngot {} items {statements:?}",
                                statements.len()
                            );
                    }
                },
                multiple => {
                    panic!("more than one statement was assembled: {multiple:?}");
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
        let mut rc_block =
            make_empty_rc_block_for_test(Address::from(Unsigned18Bit::from(0o020_000u16)));
        match symtab.lookup_with_op(&sym, span, &here, &mut rc_block, &context, &mut op) {
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

fn one_item_map<K, V>(key: K, value: V) -> BTreeMap<K, V>
where
    K: Ord,
{
    let mut result = BTreeMap::new();
    result.insert(key, value);
    result
}

#[test]
fn test_assemble_pass1() {
    fn single_manuscript_block_map(
        mb: ManuscriptBlock,
    ) -> BTreeMap<BlockIdentifier, ManuscriptBlock> {
        one_item_map(BlockIdentifier::from(0), mb)
    }

    let input = concat!("14\n", "☛☛PUNCH 26\n");
    let mut errors = Vec::new();
    let (source_file, _options) =
        assemble_pass1(input, &mut errors).expect("pass 1 should succeed");
    assert_eq!(errors.as_slice(), &[]);
    assert_eq!(
        source_file,
        Some(SourceFile {
            punch: Some(PunchCommand(Some(Address::from(u18!(0o26))))),
            blocks: single_manuscript_block_map(ManuscriptBlock {
                origin: None,
                statements: vec![Statement::Instruction(TaggedProgramInstruction {
                    tag: None,
                    instructions: vec![CommaDelimitedInstruction {
                        leading_commas: None,
                        instruction: UntaggedProgramInstruction {
                            span: Span::from(0..2),
                            holdbit: HoldBit::Unspecified,
                            inst: atom_to_fragment(Atom::Literal(LiteralValue::from((
                                Span::from(0..2),
                                Script::Normal,
                                u36!(0o14)
                            ))))
                        },
                        trailing_commas: None,
                    }]
                })]
            }),
            macros: Vec::new(), // no macros
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
        location: _,
        statements,
    }] = directive
        .blocks
        .values()
        .cloned()
        .collect::<Vec<_>>()
        .as_slice()
    {
        if let [Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instructions: first_instructions,
        }), Statement::Instruction(TaggedProgramInstruction {
            tag: None,
            instructions: second_instructions,
        })] = statements.as_slice()
        {
            if let [first_instruction] = first_instructions.as_slice() {
                if let [second_instruction] = second_instructions.as_slice() {
                    assert_eq!(first_instruction.leading_commas, None);
                    assert_eq!(first_instruction.trailing_commas, None);
                    assert_eq!(second_instruction.leading_commas, None);
                    assert_eq!(second_instruction.trailing_commas, None);

                    assert_eq!(
                        &first_instruction.instruction.inst,
                        &InstructionFragment::from((
                            Span::from(0..2usize),
                            Script::Normal,
                            Unsigned36Bit::from(0o10_u32),
                        )),
                    );
                    assert_eq!(
                        &second_instruction.instruction.inst,
                        &InstructionFragment::from((
                            span(17..19),
                            Script::Normal,
                            Unsigned36Bit::from(0o12_u32),
                        )),
                    );
                    return;
                }
            }
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
        &InstructionFragment::Config(ConfigValue::Literal(span(0..8), u36!(0o36))),
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
    let input = "1| @sup_hash@\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o1)));
    let got = program.chunks[0].words[0];
    let expected = u36!(1).shl(30);
    assert_eq!(
        got, expected,
        "input '{input}' assembled to {got} but we expected {expected}"
    );
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
            "START| @sup_1@ FOO\n",
            "       @sup_2@ FOO\n",
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

    // Note that @plus@ is not a valid glyph.
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

#[test]
fn test_double_pipe_config_literal_correctly_shifted() {
    // The 6 here is not superscript but it should be shifted into the
    // configuration part of the assembled word, because the '‖'
    // symbol introduces a configuration syllable.
    let input = "‖6\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o6).shl(30));
}

#[test]
fn test_double_pipe_config_symbolic_default_assignment() {
    // Section 6-2.2 "SYMEX DEFINITON - TAGS - EQUALITIES - AUTOMATIC
    // ASSIGNMENT" of the Users Handbook states that a symex used only
    // as a configuration value which has no defintiion will be
    // automatically assigned as zero.
    //
    // In our example here, the 42 octal should go in the address part
    // of the word.
    let input = "‖X 42\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    assert_eq!(program.chunks[0].words[0], u36!(0o42));
}

#[test]
fn test_undefined_address_only_symbols_get_rc_block_allocation() {
    // Our program contains only references to a symbol (in address
    // context) which is not defined.  Per the Users Handbook, section
    // 6-2.2 ("SYMEX DEFINITION - TAGS - EQUALITIES - AUTOMATIC
    // ASSIGNMENT") the defautl value shoudl be the numerical location
    // of the next place in the RC words block.
    //
    // However, when we see the same symbol a second time we should
    // not assign a second RC-word.
    let input = "100|X\nX\n";
    // The input should be assembled at locations 0o100 and 0o101.  So
    // the RC block should begin at location 0o102.  Hence addresses
    // 0o100 and 0o101 should both contain the value 0o102 (which is
    // the value of X).
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Check that the program was assembled at the right location
    // (otherwise, the remaining checks will not make sense).
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));

    // The RC-block should be allocated, so there should be two chunks.
    assert_eq!(program.chunks.len(), 2);

    // Verify that both uses of X refer to the same location.
    assert_eq!(program.chunks[0].words[0], u36!(0o102));
    assert_eq!(program.chunks[0].words[1], u36!(0o102));

    // The allocated RC-word should initially contain zero.
    assert_eq!(program.chunks[1].words[0], u36!(0));
}

#[test]
fn test_200_200_200_200_with_no_commas() {
    // This example is from section 6-2.4 "NUMERICAL FORMAT - USE OF
    // COMMAS" in the Users Handbook.
    //
    // Note that we don't have spaces in the input.  I believe this is
    // because the spaces in the Users Handbook are intended not to be
    // taken literally.  Otherwise it's unclear how to distinguish
    // inputs like "200 200 200 200" (from the space-separated parts
    // go into Q4 Q3 Q2 Q1) from inputs like "ADD X" where the values
    // generated from ADD and from X are assembled into the 36-bit
    // word as-is).
    let input = "200200200200\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o200200200200));
}

#[test]
fn test_200_200_200_200_with_commas() {
    // This example is from section 6-2.4 "NUMERICAL FORMAT - USE OF
    // COMMAS" in the Users Handbook.
    //
    // Note that we don't have spaces in the input.  I believe this is
    // because the spaces in the Users Handbook are intended not to be
    // taken literally.  Otherwise it's unclear how to distinguish
    // inputs like "200 200 200 200" (from the space-separated parts
    // go into Q4 Q3 Q2 Q1) from inputs like "ADD X" where the values
    // generated from ADD and from X are assembled into the 36-bit
    // word as-is).
    let input = "200,200,,200,200\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o200200200200));
}

#[test]
fn test_440_330_220_110_with_commas() {
    let input = "440,330,,220,110\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o440330220110));
}

#[test]
fn test_alternate_base_with_commas() {
    let input = "10·,11·,,12,13· ** Note that 12 is in the default, octal, base\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o012_013_012_015));
}

#[test]
fn test_440_330_220_110_with_commas_in_rc_word() {
    let input = "{440,330,,220,110}\n";
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);
    assert_eq!(program.chunks.len(), 2); // one regular chunk plus RC-block
    assert_eq!(program.chunks[0].words[0], program.chunks[1].address); // point to first word in RC-block
    assert_eq!(program.chunks[1].words[0], u36!(0o440330220110));
}
