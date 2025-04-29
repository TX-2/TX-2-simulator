use std::fmt::{Display, Write};
use std::num::IntErrorKind;

use base::prelude::*;

use super::super::{ast::*, span::Span, state::NumeralMode};

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
    sign: Option<Sign>,
    digits: &str,
    hasdot: bool,
    state: &NumeralMode,
) -> Result<Unsigned36Bit, StringConversionFailed> {
    make_u36(digits, state.radix(hasdot)).map(|n| {
        if let Some(Sign::Minus) = sign {
            Unsigned36Bit::ZERO.wrapping_sub(n)
        } else {
            n
        }
    })
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

pub(super) fn manuscript_lines_to_source_file<'a>(
    lines: Vec<(Span, ManuscriptLine)>,
) -> Result<SourceFile, chumsky::error::Rich<'a, super::super::lexer::Token>> {
    let mut blocks: Vec<ManuscriptBlock> = Vec::new();
    let mut equalities: Vec<Equality> = Vec::new();
    let mut macros: Vec<MacroDefinition> = Vec::new();
    let mut current_statements: Vec<(Span, TaggedProgramInstruction)> = Vec::new();
    let mut maybe_punch: Option<PunchCommand> = None;
    let mut effective_origin: Option<Origin> = None;

    fn ship_block(
        statements: &[(Span, TaggedProgramInstruction)],
        maybe_origin: Option<Origin>,
        result: &mut Vec<ManuscriptBlock>,
    ) {
        if !statements.is_empty() {
            result.push(ManuscriptBlock {
                origin: maybe_origin,
                statements: statements.to_vec(),
            });
        }
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

    for (span, line) in lines {
        match line {
            ManuscriptLine::TagsOnly(tags) => {
                pending_tags.extend(tags);
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::Punch(punch)) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                maybe_punch = Some(punch);
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::BaseChange(_)) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                // These already took effect on the statements which
                // were parsed following them, so no need to keep them
                // now.
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::Macro(macro_def)) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                macros.push(macro_def);
            }
            ManuscriptLine::OriginOnly(origin) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                ship_block(&current_statements, effective_origin, &mut blocks);
                current_statements.clear();
                effective_origin = Some(origin.clone());
            }
            ManuscriptLine::StatementOnly(mut tagged_program_instruction) => {
                prepend_tags(&mut tagged_program_instruction.tags, &mut pending_tags);
                current_statements.push((span, tagged_program_instruction));
            }
            ManuscriptLine::OriginAndStatement(origin, statement) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                ship_block(&current_statements, effective_origin, &mut blocks);
                current_statements.clear();
                effective_origin = Some(origin.clone());

                current_statements.push((span, statement));
            }
            ManuscriptLine::Eq(equality) => {
                if let Some(t) = pending_tags.pop() {
                    return Err(bad_tag_pos(t));
                }
                equalities.push(equality);
            }
        }
    }
    if let Some(t) = pending_tags.pop() {
        return Err(bad_tag_pos(t));
    }

    ship_block(&current_statements, effective_origin, &mut blocks);
    current_statements.clear();

    Ok(SourceFile {
        punch: maybe_punch,
        blocks,
        equalities,
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
