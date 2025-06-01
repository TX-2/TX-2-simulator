use std::collections::BTreeMap;
use std::fmt::{Display, Write};
use std::num::IntErrorKind;

use tracing::{event, Level};

use base::prelude::*;

use super::super::{ast::*, span::Span, state::NumeralMode, symbol::SymbolName};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) enum Sign {
    Plus,
    Minus,
}

impl Display for Sign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char(match self {
            Sign::Plus => '+',
            Sign::Minus => '-',
        })
    }
}

pub(super) fn make_u36(s: &str, radix: u32) -> Result<Unsigned36Bit, StringConversionFailed> {
    match u64::from_str_radix(s, radix) {
        Ok(n) => n.try_into().map_err(StringConversionFailed::Range),
        Err(e) => match e.kind() {
            IntErrorKind::Empty => Err(StringConversionFailed::EmptyInput),
            IntErrorKind::InvalidDigit => {
                match s.chars().find(|ch| ch.to_digit(radix).is_none()) {
                    Some(ch) => Err(StringConversionFailed::NotOctal(ch)),
                    None => {
                        panic!("at least one character of '{s}' is known to be invalid in base {radix}");
                    }
                }
            }
            IntErrorKind::PosOverflow => {
                Err(StringConversionFailed::Range(ConversionFailed::TooLarge))
            }
            _ => unreachable!(),
        },
    }
}

#[test]
fn test_make_u36() {
    assert_eq!(Ok(u36!(0)), make_u36("0", 8));
    assert_eq!(Ok(u36!(0)), make_u36("+0", 8));
    assert_eq!(Ok(u36!(1)), make_u36("1", 8));
    assert_eq!(Ok(u36!(1)), make_u36("1", 10));
    assert_eq!(Ok(u36!(1)), make_u36("+1", 8));
    assert_eq!(Ok(u36!(1)), make_u36("+1", 8));
    assert!(make_u36("+1+1", 8).is_err());
    assert!(make_u36("18", 8).is_err());
    assert!(make_u36("19", 8).is_err());
    assert_eq!(Ok(u36!(19)), make_u36("19", 10));
}

pub(crate) fn make_num(
    digits: &str,
    hasdot: bool,
    state: &NumeralMode,
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_u36(digits, state.radix(hasdot))
}

pub(super) fn punch_address(a: Option<LiteralValue>) -> Result<PunchCommand, String> {
    match a {
        None => Ok(PunchCommand(None)),
        Some(literal) => {
            let value = literal.value();
            match Unsigned18Bit::try_from(value) {
                Err(e) => Err(format!(
                    "PUNCH address value {:o} is not a valid address: {}",
                    value, e
                )),
                Ok(halfword) => {
                    let addr: Address = Address::from(halfword);
                    if addr.mark_bit() != Unsigned18Bit::ZERO {
                        Err(format!(
                            "PUNCH address value {:o} must not be a deferred address",
                            addr
                        ))
                    } else {
                        Ok(PunchCommand(Some(addr)))
                    }
                }
            }
        }
    }
}

fn expand_macro(
    invocation: &MacroInvocation,
    macros: &BTreeMap<SymbolName, MacroDefinition>,
) -> InstructionSequence {
    invocation.substitute_macro_parameters(macros)
}

pub(super) fn manuscript_lines_to_source_file<'a>(
    lines: Vec<(Span, ManuscriptLine)>,
) -> Result<SourceFile, chumsky::error::Rich<'a, super::super::lexer::Token>> {
    let mut blocks: Vec<ManuscriptBlock> = Vec::new();
    let mut equalities: Vec<Equality> = Vec::new();
    let mut macros: BTreeMap<SymbolName, MacroDefinition> = Default::default();
    let mut maybe_punch: Option<PunchCommand> = None;

    fn get_or_create_output_block(result: &mut Vec<ManuscriptBlock>) -> &mut ManuscriptBlock {
        if result.is_empty() {
            result.push(ManuscriptBlock {
                origin: None,
                sequences: Vec::new(),
            });
        }
        result
            .last_mut()
            .expect("result cannot be empty because we just pushed an item onto it")
    }

    fn begin_new_block(origin: Origin, result: &mut Vec<ManuscriptBlock>) -> &mut ManuscriptBlock {
        result.push(ManuscriptBlock {
            origin: Some(origin),
            sequences: Vec::new(),
        });
        result
            .last_mut()
            .expect("result cannot be empty because we just pushed an item onto it")
    }

    fn prepend_tags(v: &mut Vec<Tag>, initial: &mut Vec<Tag>) {
        let alltags: Vec<Tag> = initial.drain(0..).chain(v.drain(0..)).collect();
        v.extend(alltags);
    }

    let mut pending_tags: Vec<Tag> = Vec::new();

    let bad_tag_pos = |tag: Tag| {
        let tag_name = &tag.name;
        chumsky::error::Rich::custom(
            tag.span,
            format!("tag {tag_name} must be followed by an instruction"),
        )
    };

    for (_span, line) in lines {
        match line {
            ManuscriptLine::Macro(invocation) => {
                get_or_create_output_block(&mut blocks)
                    .sequences
                    .push(expand_macro(&invocation, &macros));
            }
            ManuscriptLine::TagsOnly(tags) => {
                pending_tags.extend(tags);
            }

            ManuscriptLine::Meta(_)
            | ManuscriptLine::OriginOnly(_)
            | ManuscriptLine::OriginAndStatement(_, _)
            | ManuscriptLine::Eq(_)
                if !pending_tags.is_empty() =>
            {
                return Err(bad_tag_pos(
                    pending_tags
                        .pop()
                        .expect("we know pending_tags is non-empty"),
                ));
            }

            ManuscriptLine::Meta(ManuscriptMetaCommand::Punch(punch)) => {
                maybe_punch = Some(punch);
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::BaseChange(_)) => {
                // These already took effect on the statements which
                // were parsed following them, so no need to keep them
                // now.
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::Macro(macro_def)) => {
                if let Some(previous) = macros.insert(macro_def.name.clone(), macro_def) {
                    event!(Level::INFO, "Redefinition of macro {}", &previous.name);
                }
            }

            ManuscriptLine::OriginOnly(origin) => {
                begin_new_block(origin, &mut blocks);
            }
            ManuscriptLine::StatementOnly(mut tagged_program_instruction) => {
                prepend_tags(&mut tagged_program_instruction.tags, &mut pending_tags);
                get_or_create_output_block(&mut blocks)
                    .push_unscoped_instruction(tagged_program_instruction);
            }
            ManuscriptLine::OriginAndStatement(origin, statement) => {
                begin_new_block(origin, &mut blocks).push_unscoped_instruction(statement);
            }
            ManuscriptLine::Eq(equality) => {
                equalities.push(equality);
            }
        }
    }
    if let Some(t) = pending_tags.pop() {
        return Err(bad_tag_pos(t));
    }

    Ok(SourceFile {
        punch: maybe_punch,
        blocks,
        global_equalities: equalities,
        macros,
    })
}

/// Some instructions are assembled with the hold bit automatically
/// set.  These are JPX, JNX, LDE, ITE.  See Users Handbook, section
/// 4-3.2 on page 4-5.
pub(super) fn opcode_auto_hold_bit(opcode: Unsigned6Bit) -> u64 {
    if matches!(u8::from(opcode), 0o06 | 0o07 | 0o20 | 0o40) {
        1 << 35
    } else {
        0
    }
}

pub(super) fn is_register_name(name: &str) -> bool {
    matches!(name, "A" | "B" | "C" | "D" | "E")
}
