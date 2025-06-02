use std::ops::{Range, Shl};

use super::super::ast::{
    ArithmeticExpression, Atom, CommaDelimitedFragment, HoldBit, InstructionFragment,
    InstructionSequence, LiteralValue, LocatedBlock, ManuscriptBlock, PunchCommand, SourceFile,
    TaggedProgramInstruction, UntaggedProgramInstruction,
};
use super::super::collections::OneOrMore;
use super::super::eval::{
    lookup_with_op, make_empty_rc_block_for_test, EvaluationContext, SymbolValue,
};
use super::super::span::*;
use super::super::symbol::SymbolName;
use super::super::symtab::IndexRegisterAssigner;
use super::{assemble_nonempty_valid_input, assemble_source};
use super::{assemble_pass1, Binary, BinaryChunk};
use base::{
    charset::Script,
    prelude::{
        u18, u36, u6, Address, Instruction, Opcode, OperandAddress, SymbolicInstruction,
        Unsigned18Bit, Unsigned36Bit, Unsigned5Bit, Unsigned6Bit,
    },
};

#[cfg(test)]
fn assemble_check_symbols(input: &str, target_address: Address, expected: &[(&str, SymbolValue)]) {
    use crate::eval::HereValue;

    let (_directive, mut explicit_symbols, mut implicit_symbols, mut memory_map, _) =
        assemble_nonempty_valid_input(input);

    for (name, expected_value) in expected.iter() {
        let sym = SymbolName {
            canonical: name.to_string(),
        };
        let span = span(0..(name.len()));
        let mut rc_block =
            make_empty_rc_block_for_test(Address::from(Unsigned18Bit::from(0o020_000u16)));

        let mut index_register_assigner: IndexRegisterAssigner = IndexRegisterAssigner::default();
        let mut ctx = EvaluationContext {
            explicit_symtab: &mut explicit_symbols,
            implicit_symtab: &mut implicit_symbols,
            memory_map: &mut memory_map,
            here: HereValue::Address(target_address),
            index_register_assigner: &mut index_register_assigner,
            rc_updater: &mut rc_block,
            lookup_operation: Default::default(),
        };

        match lookup_with_op(&mut ctx, &sym, span) {
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
    // Given a program containing a constant and a PUNCH metacommand
    let input = concat!("14\n", "☛☛PUNCH 26\n");

    // When we assemble it
    let mut errors = Vec::new();
    let (source_file, _options) =
        assemble_pass1(input, &mut errors).expect("pass 1 should succeed");

    // Then we should see that it assembles without error, and...
    assert_eq!(errors.as_slice(), &[]);
    assert_eq!(
        source_file,
        Some(SourceFile {
            // .. that the punch directive was correctly recorded, and...
            punch: Some(PunchCommand(Some(Address::from(u18!(0o26))))),
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![InstructionSequence {
                    local_symbols: None,
                    instructions: vec![TaggedProgramInstruction {
                        span: span(0..2),
                        tags: Vec::new(),
                        instruction: UntaggedProgramInstruction {
                            fragments: OneOrMore::new(CommaDelimitedFragment {
                                leading_commas: None,
                                holdbit: HoldBit::Unspecified,
                                span: span(0..2),
                                fragment: atom_to_fragment(Atom::from(LiteralValue::from((
                                    Span::from(0..2),
                                    Script::Normal,
                                    // ... that the constant was correctly assembled.
                                    u36!(0o14)
                                )))),
                                trailing_commas: None,
                            })
                        }
                    }]
                }],
            }],
            global_equalities: Default::default(), // no equalities
            macros: Default::default(),            // no macros
        })
    );
}

fn span(range: Range<usize>) -> Span {
    Span::from(range)
}

#[test]
fn test_metacommand_dec_changes_default_base() {
    // Given a program which uses the value 10 once in octal and then
    // once in decimal
    const INPUT: &str = concat!("10\n", "☛☛DECIMAL\n", "10  ** Ten\n");

    // When we assemble it
    let (directive, _, _, _, index_register_assigner) = assemble_nonempty_valid_input(INPUT);
    assert!(
        index_register_assigner.is_empty(),
        "no index register should have been default-assigned"
    );

    if let [LocatedBlock {
        origin: _,
        location: _,
        sequences,
    }] = directive.blocks.values().collect::<Vec<_>>().as_slice()
    {
        if let [InstructionSequence {
            local_symbols: None,
            instructions,
        }] = sequences.as_slice()
        {
            if let [TaggedProgramInstruction {
                span: _,
                tags: tags1,
                instruction: first_instruction,
            }, TaggedProgramInstruction {
                span: _,
                tags: tags2,
                instruction: second_instruction,
            }] = instructions.as_slice()
            {
                assert!(tags1.is_empty());
                assert!(tags2.is_empty());

                let first_fragment = first_instruction.fragments.first();
                let second_fragment = second_instruction.fragments.first();

                assert_eq!(first_fragment.leading_commas, None);
                assert_eq!(first_fragment.trailing_commas, None);
                assert_eq!(second_fragment.leading_commas, None);
                assert_eq!(second_fragment.trailing_commas, None);

                // Then we should see that the first value is assembled as 10 octal...
                assert_eq!(
                    &first_fragment.fragment,
                    &InstructionFragment::from((
                        Span::from(0..2usize),
                        Script::Normal,
                        Unsigned36Bit::from(0o10_u32),
                    )),
                );
                // ... and that the first value is assembled as 12
                // octal (10 decimal).
                assert_eq!(
                    &second_fragment.fragment,
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
    panic!(
        "expected two items with value 10 octal and 12 octal, got {:?}",
        &directive,
    );
}

#[test]
fn test_assignment_rhs_is_instruction() {
    // The RHS of an assignment can be "any 36-bit value" (see TX-2
    // Users Handbook, section 6-2.2, page 156 = 6-6).  Here we verify
    // that it can be an instruction.
    assemble_check_symbols(
        // Given a program using an instruction as an equality value,
        // when we assemble it
        concat!(
            "FOO=²¹IOS₅₂ 30106  ** FROM PLUGBOARD A AT ADDRESS 377762\n",
            "** WE USE FOO TO MAKE SURE THE SYMBOL VALUE IS NEEDED\n",
            "** (AND HENCE IS RETAINED).\n",
            "FOO\n"
        ),
        Address::ZERO,
        // Then we should see that the symbol was assigned the value
        // corresponding to the assembled value of that instruction.
        &[("FOO", SymbolValue::Final(u36!(0o210452_030106)))],
    );
}

#[test]
fn test_normal_hash_value() {
    // Given a program which uses the value of # ("here") in the
    // instruction at address 101, when we assemble it
    let program = assemble_source("100| 2\n#\n", Default::default()).expect("program is valid");

    // Then we should see that # was evaluated as the address (101) at
    // which it was evaluated.
    assert_eq!(program.chunks[0].words[1], u36!(0o101));
}

#[test]
fn test_super_hash_value() {
    // Given a program which assembles at address 1 the value of # ("here")
    let input = "1| @sup_hash@\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");

    // Then we should see that the program is assembled at the correct address...
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o1)));
    // ... and that the resulting value has shifted the value of #
    // (which should be 1) into the correct (i.e. configuration field)
    // position in the resulting word.
    let got = program.chunks[0].words[0];
    let expected = u36!(1).shl(30);
    assert_eq!(
        got, expected,
        "input '{input}' assembled to {got} but we expected {expected}"
    );
}

#[test]
fn test_sub_hash_value() {
    // Given a program which assembles at address 1 the value of # ("here"), when we assemble it
    let program =
        assemble_source(concat!("1| @sub_hash@\n",), Default::default()).expect("program is valid");

    // Then we should see that # evaluates as 1, the address of the
    // insruction containing it.
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

    // Given a program which uses # on the right-hand-side of an
    // equality, when we assemble it
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
    // Then we should see that the value of the assigned symbol
    // depends on the address at which it is used.
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
    // Given a program which contains the constant 6∧2 (in binary,
    // 110∧10), when we assemble it (bearing in mind that ∧ is the
    // logical-and operator)
    let program1 = assemble_source("100| 6 ∧ 2\n", Default::default()).expect("program is valid");
    // Then we should get the result 2 (binary 10).
    assert_eq!(program1.chunks[0].words[0], u36!(0o2));

    // This is the same test as above, but using @and@ instead of its
    // synonym ∧.
    let program2 =
        assemble_source("100| 6 @and@ 4\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o4));
}

#[test]
fn test_addition_on_constants() {
    // Given a program which contains the constant 6+2, when we assemble it
    let program1 = assemble_source("100| 6 + 2\n", Default::default()).expect("program is valid");
    // Then we should obtain the result 8 (10 octal).
    assert_eq!(program1.chunks[0].words[0], u36!(0o10));

    // This case is identical to the above, but using @add@ instead of
    // +.  These should be synonyms.  Note that @plus@ is not a valid
    // glyph.
    let program2 =
        assemble_source("100| 6 @add@ 2\n", Default::default()).expect("program is valid");
    assert_eq!(program2.chunks[0].words[0], u36!(0o10));
}

#[test]
fn test_subtraction_on_constants() {
    // Given a program which contains the constant 6-2, when we assemble it
    let program1 = assemble_source("100| 6 - 2\n", Default::default()).expect("program is valid");

    // Then we should obtain the result 4
    assert_eq!(program1.chunks[0].words[0], u36!(0o4));
}

#[test]
fn test_multiplication_on_constants() {
    // Given a program containing a constant 6x2, when we assemble it
    let program1 =
        assemble_source("100| 6 @times@ 2\n", Default::default()).expect("program is valid");
    // Then we should obtain the result 12 (14 octal).
    assert_eq!(program1.chunks[0].words[0], u36!(0o14));

    // Given a program containing the constant 6x3, when we assemble it
    let program2 = assemble_source("100| 6×3\n", Default::default()).expect("program is valid");
    // Then we should obtain the result 18 (22 octal).
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

    // Given a program which uses the double-pipe symbol to introduce
    // a configuration value
    let input = "‖6\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");

    // Then we should see that the configuration value ends up in the
    // correct place in the assembled word.
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

    // Given a program which uses the double-pipe symbol to indicate a
    // configuration value, using a symbol which is not defined
    let input = "‖X 42\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");

    // Then we should see that the symbol is default-assigned as zero.
    assert_eq!(program.chunks[0].words[0], u36!(0o42));
}

#[test]
fn test_undefined_address_only_symbols_get_rc_block_allocation() {
    // Our program contains only references to a symbol (in address
    // context) which is not defined.  Per the Users Handbook, section
    // 6-2.2 ("SYMEX DEFINITION - TAGS - EQUALITIES - AUTOMATIC
    // ASSIGNMENT") the default value should be the numerical location
    // of the next place in the RC words block.
    //
    // However, when we see the same symbol a second time we should
    // not assign a second RC-word.

    // Given a program which refers twicve to a symbol having no
    // definition
    let input = "100|X\nX\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see that the symbol was given a default
    // definition exactly once.

    // The input should be assembled at locations 0o100 and 0o101.  So
    // the RC block should begin at location 0o102.  Hence addresses
    // 0o100 and 0o101 should both contain the value 0o102 (which is
    // the value of X).

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

    // Given a program containing a 36-bit constant word
    let input = "200200200200\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see the that the word is evaluated as the
    // correct value.
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

    // Given a program which uses a comma expression
    let input = "200,200,,200,200\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see that the comma expression is correctly
    // evaluated
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o200200200200));
}

#[test]
fn test_440_330_220_110_with_commas() {
    // Given a program which uses a comma expression
    let input = "440,330,,220,110\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see that the comma expression was correctly evaluated
    assert_eq!(program.chunks.len(), 1); // one chunk (no RC-block needed).
    assert_eq!(program.chunks[0].words[0], u36!(0o440330220110));
}

#[test]
fn test_alternate_base_with_commas() {
    assert_eq!(
        // Given a literal which uses both decimal and octal bases, when we assemble it
        assemble_source(
            "10·,11·,,12,13· ** Note that 12 is in the default, octal, base\n",
            Default::default(),
        ),
        Ok(Binary {
            entry_point: None,
            chunks: vec![BinaryChunk {
                address: Address::from(u18!(0o00200000)),
                // Then the assembled value should show that the
                // conversions were carried out in the correct bases.
                words: vec![u36!(0o012_013_012_015)]
            }]
        })
    );
}

#[test]
fn test_440_330_220_110_with_commas_in_rc_word() {
    // Given a program which assembles a comma-expression inside an RC-word
    let input = "{440,330,,220,110}\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see that the program code refers to the RC-word
    // by its address, and the RC-word contains the literal value we
    // put in the braces.
    assert_eq!(program.chunks.len(), 2); // one regular chunk plus RC-block
    assert_eq!(program.chunks[0].words[0], program.chunks[1].address); // point to first word in RC-block
    assert_eq!(program.chunks[1].words[0], u36!(0o440330220110));
}

#[test]
fn test_here_in_rc_word() {
    // Given a program which uses # in an RC-word
    let input = "100|{#}\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then the RC-word's value should show that # was evaluated as
    // the address of the RC-word itself, not the address of the
    // instruction whcih refers to the RC-word.
    assert_eq!(program.chunks.len(), 2); // one regular chunk plus RC-block
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));
    assert_eq!(program.chunks[0].words.len(), 1);
    assert_eq!(program.chunks[0].words[0], u36!(0o101)); // points to first word in RC-block

    assert_eq!(program.chunks[1].address, Address::from(u18!(0o101)));
    assert_eq!(program.chunks[1].words.len(), 1); // RC block has one word
    assert_eq!(program.chunks[1].words[0], u36!(0o101)); // # is 0o101 at address 0o101
}

#[test]
fn test_here_in_nested_rc_word_simplistic() {
    // This test makes some assumptions about the order in which
    // RC-words are allocated.  Therefore there are some correct
    // assembler implementations which might not pass this test.
    //
    // See also test_here_in_nested_rc_word_careful() for a more
    // careful test which is on the other hand not so easy to diagnose
    // when it fails.

    // Given a program which nests one RC-word inside another
    let input = "100|{{#+400}}\n";

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should obtain a program in which the program refers to
    // the outer RC-word, and the outer RC-word gets allocated at a
    // lower address than the inner RC-word.
    assert_eq!(program.chunks.len(), 2); // one regular chunk plus RC-block
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));
    assert_eq!(program.chunks[0].words.len(), 1);
    assert_eq!(program.chunks[0].words[0], u36!(0o101)); // points to first word in RC-block

    assert_eq!(program.chunks[1].address, Address::from(u18!(0o101)));
    assert_eq!(program.chunks[1].words.len(), 2);
    // The first RC-word points to the second RC-word.
    assert_eq!(program.chunks[1].words[0], u36!(0o102));
    // # is 0o102 at address 0o102, so #+400 is 0o502.
    assert_eq!(program.chunks[1].words[1], u36!(0o502));
}

#[test]
fn test_here_in_nested_rc_word_careful() {
    // This test is a little complex because out real requirenent is
    // that the outer RC-word points to the inner RC-word and that the
    // inner RC-word contains the right content.  But we don't
    // specifically require these RC-words to be allocated within the
    // RC-block in any particular order.
    //
    // See also test_here_in_nested_rc_word_simplistic() which is a
    // version of this test which is easier to understand but might
    // reject some correct implementations.

    // Given a program which contains an RC-word nested inside another
    // RC-word, and in which the inner RC-word refers to its own
    // address.
    let input = "100|{{#+400}}\n";

    fn rc_word_at_addr(addr: Unsigned36Bit, rcwords: &BinaryChunk) -> Option<&Unsigned36Bit> {
        match addr.checked_sub(rcwords.address.into()) {
            None => {
                panic!("failed to subtract {} from {addr}", rcwords.address);
            }
            Some(x) => match Unsigned18Bit::try_from(x) {
                Err(_) => {
                    panic!("failed to convert {x} into an Unsigned18Bit value");
                }
                Ok(x) => {
                    let offset: usize = x.into();
                    rcwords.words.get(offset)
                }
            },
        }
    }

    // When we assemble that program
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then the program should contain a program chunk containing one
    // word, and a second chunk (the RC block) containing two words.
    //
    // Then also (and this is the key part of this test) the outer
    // RC-block should refer to the inner RC-block, and the inner
    // RC-block should show that # was evaluated to the address of the
    // inner RC-word.
    assert_eq!(program.chunks.len(), 2); // one regular chunk plus RC-block
    assert_eq!(program.chunks[0].words.len(), 1);
    assert_eq!(program.chunks[1].words.len(), 2);
    assert_eq!(program.chunks[0].address, Address::from(u18!(0o100)));
    assert_eq!(program.chunks[1].address, Address::from(u18!(0o101)));
    // In the program code there should be a reference into the RC block.
    let first_ref = program.chunks[0].words[0];

    // The RC word that the program code points directly to contains a
    // reference to another RC word.
    let inner_location: Unsigned36Bit = match rc_word_at_addr(first_ref, &program.chunks[1]) {
        Some(w) => *w,
        None => {
            panic!("unable to find an RC word at address {first_ref}");
        }
    };
    match rc_word_at_addr(inner_location, &program.chunks[1]) {
        Some(w) => {
            let expected = inner_location
                .checked_add(u36!(0o400))
                .expect("should not overflow");
            assert_eq!(*w, expected);
        }
        None => {
            panic!("outer RC-word does not point to inner RC-word");
        }
    }
}

#[test]
fn tag_definition_in_rc_word() {
    // Tag values in RC-words are not "local" to the RC-word.
    //
    // Tags defined in RC-words may not be used for M4's editing
    // instuctions, but nevertheless they are not locally-scoped.
    // This is demonstrated by the example in section 6-4.7 of the
    // User's Handbook, which looks like this:
    //
    // ```
    // ☛☛DEF TBS|α
    //  α
    //  α
    //  α
    //  α
    //  α
    // ☛☛EMD
    // 100|
    // USE->     LDA {TS->TBS|0}  ** 5 BLANK RC WORDS
    //           LDA TOMM
    //           STA TS+3
    // ```
    //
    // You will see above that the definition of the tag `TS` is
    // inside an RC-word, but _not_ inside a macro body.
    //
    // The example explains that the above code snippet expands to:
    //
    // ```
    // 100|
    // USE ->    LDA {TS-> TBS| 0}              |002400 000103|000100
    //           LDA TOMM                       |002400 000110|   101
    //           STA TS+3                       |003400 000106|   102
    // TS ->     TBS 0
    //           0                              |000000 000000|   103
    //           0                              |000000 000000|   104
    //           0                              |000000 000000|   105
    //           0                              |000000 000000|   106
    //           0                              |000000 000000|   107
    // TOMM ->   0                              |000000 000000|000110
    // ```
    //
    // We cannot yet use the above example as our test case as macro
    // expansion is not yet supported.

    // Given a program which defines a tag inside an RC-word (but not
    // inside a macro body)
    let input = concat!(
        "100| {T->200}\n", // address 100=103 (address of the first RC-word)
        "     T\n",        // address 101=103 (global value of T)
        "     {T}\n"       // address 102=104 (address of second RC-word)
    );

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should see that the tag value is accessible in the main
    // body of the program, and is also accessible in other RC-words.
    assert_eq!(
        program,
        Binary {
            entry_point: None,
            chunks: vec![
                BinaryChunk {
                    address: Address::from(u18!(0o100)),
                    words: vec![
                        u36!(0o103), // From address of RC-word containing "T->200".
                        u36!(0o103), // The value of T is global
                        u36!(0o104), // from "{T}"
                    ]
                },
                BinaryChunk {
                    // This is the RC-block.
                    address: Address::from(u18!(0o103)),
                    words: vec![
                        u36!(0o200), // First RC-word (which also defines T)
                        u36!(0o103), // Second RC-word contains the value of T.
                    ]
                }
            ]
        }
    );
}

#[test]
fn default_assigned_rc_word() {
    // See section 6-2.2 of the User Handbook for a description of how
    // this is supposed to work.
    //
    // It states that for symexes used only in an address context, the
    // default assignment is,
    //
    // The numerical memory location of the next place in the RC words
    // block. The contents of this RC word are set to zero.  This
    // provision is useful in assigning temporary storage.

    // Given a program which uses two symbols TEMP1 and TEMP2 without defining them.
    // When we assemble it...
    let program = assemble_source("100| STA TEMP1\n     STB TEMP2\n", Default::default())
        .expect("program is valid");

    // Then we should find that these symbols were assigned as
    // RC-words.
    assert_eq!(
        program,
        Binary {
            entry_point: None,
            chunks: vec![
                BinaryChunk {
                    address: Address::from(u18!(0o100)),
                    words: vec![
                        // The STA instruction
                        Instruction::from(&SymbolicInstruction {
                            held: false,
                            configuration: Unsigned5Bit::ZERO,
                            opcode: Opcode::Sta,
                            index: Unsigned6Bit::ZERO,
                            // TEMP1 is assigned as the first RC-word
                            operand_address: OperandAddress::Direct(Address::from(u18!(0o102))),
                        })
                        .bits(),
                        // The STB instruction
                        Instruction::from(&SymbolicInstruction {
                            held: false,
                            configuration: Unsigned5Bit::ZERO,
                            opcode: Opcode::Stb,
                            index: Unsigned6Bit::ZERO,
                            // TEMP2 is assigned as the second RC-word
                            operand_address: OperandAddress::Direct(Address::from(u18!(0o103))),
                        })
                        .bits()
                    ]
                },
                BinaryChunk {
                    // The RC block
                    address: Address::from(u18!(0o102)),
                    // Both RC-words should be initialised as zero.
                    words: vec![Unsigned36Bit::ZERO, Unsigned36Bit::ZERO,]
                }
            ]
        }
    );
}

#[test]
fn default_assigned_index_register_easy_case() {
    // See section 6-2.2 of the User Handbook for a description of how
    // this is supposed to work.
    //
    // It states that for symexes used only in an index register
    // context, the default assignment is, "The lowest numerical index
    // register value not already used.  Except zero and no higher
    // than 77."
    //
    // It's not clear what "not already used" really means.  For
    // example, in this program:
    //
    // STAⱼ 0
    // STAₖ 0
    //
    // It seems clear that j and k would be default-addiend to 1 and 2
    // respectively.  But suppose instead that the program looked like
    // this:
    //
    // STA₁ 0  ** USES INDEX REGISTER 1
    // STAⱼ 0  ** SHOULD j BE DEFAULT ASSIGNED as 1 or 2?
    //
    // Here, index register 1 is used by the first instruction.  Does
    // index register 1 count as used?
    //
    // This test uses the first program above.  IOW it doesn't assume
    // any particular answer to the second question.
    //
    // But, if the intent was that we would avoid assigning j=1 in the
    // case above, a somewhat legalistic interpretation would be that
    // any use of hardware-specific sequence 65 (LW input) would cause
    // the assembler to default-assign 66 (which is also a hardware
    // device, LW output).  That doesn't seem very useful.

    // Given a program which uses symbolic index values j and k in
    // that order, when we assemble it
    let program =
        assemble_source("100|STAⱼ 0\nSTAₖ 0\n", Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should obtain a program which shows that j and k were
    // default-assigned with values 1 and 2 respectively.
    assert_eq!(program.chunks.len(), 1, "wrong number of program chunks");
    assert_eq!(
        SymbolicInstruction::try_from(&Instruction::from(program.chunks[0].words[0]))
            .expect("first instruction should be valid"),
        SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::ZERO,
            opcode: Opcode::Sta,
            index: u6!(1), // j
            operand_address: OperandAddress::Direct(Address::from(Unsigned18Bit::ZERO)),
        }
    );
    assert_eq!(
        SymbolicInstruction::try_from(&Instruction::from(program.chunks[0].words[1]))
            .expect("second instruction should be valid"),
        SymbolicInstruction {
            held: false,
            configuration: Unsigned5Bit::ZERO,
            opcode: Opcode::Sta,
            index: u6!(2), // k
            operand_address: OperandAddress::Direct(Address::from(Unsigned18Bit::ZERO)),
        }
    );
    assert_eq!(program.chunks[0].words.len(), 2);
}

#[test]
fn test_bit_designator_evaluation_result() {
    // Given a program which uses a bit designator,
    // when we assemble it:
    let program = assemble_source("100|SKM₂․₁ 0\n", Default::default()).expect("program is valid");

    // Then we should obtain a program in which the index part of the
    // instruction holds the correct value of the bit designator.
    dbg!(&program);
    assert_eq!(program.chunks.len(), 1);
    assert_eq!(program.chunks[0].words.len(), 1);
    // SKM is opcode 0o17.  bit designator 2·1 is 0o41.  The opcode
    // gets shifted left 24 bit positions, the index value is shifted
    // left by 18 bit positions.
    assert_eq!(program.chunks[0].words[0], u36!(0o001_741_000_000));
}

#[test]
fn test_kleinrock_200016() {
    // Given a program which uses the "pipe construct"
    let input = concat!(
        "t = 6\n",
        "MKN ₄․₁₀@sub_pipe@ₜ 022122\n",
        // We manipulate the location of the RC block, so that the
        // RC-word allocated by the pipe construct is placed at
        // 206336.
        "206335|0\n",
    );

    // When we assemble it
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then we should obtain a program in which the RC-word part of
    // the pipe construct is allocated in the RC-block and contains
    // the value specified in the pipe construct.
    assert_eq!(program.chunks.len(), 3);
    assert_eq!(
        program.chunks[0].words.len(),
        1,
        "Program code has wrong length"
    );
    assert_eq!(program.chunks[2].words.len(), 1, "RC block length is wrong");

    assert_eq!(program.chunks[0].address, Address::from(u18!(0o200_000))); // Location of program code
    assert_eq!(program.chunks[0].words[0], u36!(0o031_712_606_336));

    // The placeholder block at 206335 is part of the test set-up, its
    // single word of content is not material to the test (only its
    // location is important).

    assert_eq!(program.chunks[2].address, Address::from(u18!(0o206_336))); // Location of RC-block
    assert_eq!(program.chunks[2].words[0], u36!(0o000_006_022_122)); // ₜ 022122
}

#[test]
fn test_undefined_symbol_in_calculation() {
    // Given a program which defines a symbol (A) in terms of a symbol
    // (B) which needs to be given a default definition.
    let input = concat!(
        "A = B + 2\n",
        // B is used only in an index context, so should be
        // default-assigned as 1 (being the first free index
        // register).
        "DPX @sub_B@ 4\n",
        // When we evaluate A, it should be evaluated as B+2, and so
        // it should take the value 3.
        "A\n",
    );

    // When we assemble the program
    let program = assemble_source(input, Default::default()).expect("program is valid");
    dbg!(&program);

    // Then the symbol B is assigned the correct default definition (1)
    // and the value of A is consistent with that definition (so, 3).
    assert_eq!(program.chunks.len(), 1, "no RC-block should be allocated");
    assert_eq!(program.chunks[0].words.len(), 2); // program length

    // The potential bug we care about here is the situation in which
    // evaluation of A fails (e.g. because it depends on a value which
    // needs to be default-assigned) and itself gets default-assigned
    // (which would be incorrect, since it has a definition).
    assert_eq!(program.chunks[0].words[1], u36!(0o3));
}

#[test]
fn test_symbol_definition_loop_detection() {
    use super::super::types::AssemblerFailure;
    use super::super::types::{ProgramError, WithLocation};
    // Given a program in which two symbols are defined in terms of each other
    let input = concat!("SA = SB\n", "SB = SA\n", "SA\n",);

    // When I assemble that program
    match assemble_source(input, Default::default()) {
        Err(AssemblerFailure::BadProgram(errors)) => {
            assert_eq!(
                errors.len(),
                2,
                "expected 2 errors from the assembler, but got {}: {errors:#?}",
                errors.len()
            );
            match errors.as_slice() {
                [e1 @ WithLocation {
                    location: _,
                    inner: ProgramError::SymbolDefinitionLoop { .. },
                }, e2 @ WithLocation {
                    location: _,
                    inner: ProgramError::SymbolDefinitionLoop { .. },
                }] => {
                    // Then the error messages that result should name
                    // both of the problem symbols, indicating the
                    // dependency loop for each.
                    let (msg1, msg2) = (e1.to_string(), e2.to_string());
                    let sa_msg =
                        "symbol SA is undefined because its definition forms a loop: SA->SB->SA";
                    let sb_msg =
                        "symbol SB is undefined because its definition forms a loop: SB->SA->SB";
                    dbg!(&msg1);
                    dbg!(&msg2);
                    assert!(
                        (msg1.contains(sa_msg) && msg2.contains(sb_msg))
                            || (msg1.contains(sb_msg) && msg2.contains(sa_msg)),
                        "error messages did not include the expected text:\n{msg1}\n{msg2}"
                    );
                }
                otherwise => {
                    panic!("expected an error from the assembler, but not: {otherwise:?}");
                }
            }
        }
        Err(e) => {
            panic!("expected an error from the assembler, but not this one: {e:?}");
        }
        Ok(program) => {
            panic!("expected an error from the assembler, not an assembled program: {program:?}");
        }
    }
}

#[test]
fn test_hash_evaluation() {
    // Given a program which uses the value of 'hash' at absolute
    // address 1
    let input_hash = "1| @hash@\n";
    let input_one = "1| 1\n";

    // When I assemble it
    let program_hash =
        assemble_source(input_hash, Default::default()).expect("input_b should be a valid program");
    dbg!(&program_hash);
    let program_one =
        assemble_source(input_one, Default::default()).expect("input_a should be a valid program");
    dbg!(&program_one);

    // Then I should get the same result as if I had assembled the
    // literal value 1 directly.
    assert_eq!(&program_one, &program_hash);
}

#[test]
fn test_minus_hash_evaluation() {
    // Given a program which negates the value of 'hash' at absolute
    // address 1
    let input_minus_hash = "1| -@hash@\n";
    let input_minus_one = "1| -1\n";

    // When I assemble it
    let program_minus_hash = assemble_source(input_minus_hash, Default::default())
        .expect("input_b should be a valid program");
    dbg!(&program_minus_hash);
    let program_minus_one = assemble_source(input_minus_one, Default::default())
        .expect("input_a should be a valid program");
    dbg!(&program_minus_one);

    // Then I should get the same result as assembling -1 directly.
    assert_eq!(&program_minus_one, &program_minus_hash);
}

#[test]
fn test_minus_hash_config_evaluation() {
    // Given a program which has an instruction at address 1 which
    // uses a negated hash (whose value would therefore be -1)as a
    // config value
    let input = "1| @sup_minus@@sup_hash@ 0\n";
    // And given a program which directly uses -1 as a configuration value
    let comparison_input = "1| ⁻¹ 0\n";

    // When I assemble them
    let program =
        assemble_source(input, Default::default()).expect("input_b should be a valid program");
    dbg!(&program);
    let comparison_program = assemble_source(comparison_input, Default::default())
        .expect("input_a should be a valid program");
    dbg!(&comparison_program);

    // Then these programs should assemble to identical output.
    assert_eq!(&comparison_program, &program);
}

#[test]
fn test_diagnose_duplicate_tags_in_macro_body() {
    // Given a macro that uses the same tag name for two different
    // instructions:
    let input = concat!(
        "☛☛DEF MYMACRO≡\n",
        // First tag assignment
        " T-> 2\n",
        // Second tag assignment (which is not allowed for the
        // same tag name, even inside a macro body).
        " T-> 3\n",
        "☛☛EMD",
        "\n",
        // Expand the macro just once.
        "MYMACRO≡\n",
    );

    // When I assemble a program using the macro
    let mut errors = Default::default();
    let expected_msg = "T is defined more than once";
    let r = dbg!(assemble_pass1(input, &mut errors));

    // Then the assembly should fail with a message about the
    // duplicate tag.
    match r {
        Ok((_source_file, _options)) => {
            dbg!(&errors);
            assert!(!errors.is_empty());
            assert!(errors.iter().any(|e| e.to_string().contains(expected_msg)));
        }
        Err(e) => {
            dbg!(&errors);
            dbg!(&e);
            // Although the current implementation successfully parses
            // the program but returns an error in `errors`, we also
            // accept a hypothetical implementation in which
            // assemble_pass1() returns Err.
            assert!(e.to_string().contains(expected_msg));
        }
    }
}
