use base::charset::Script;
use chumsky::input::ValueInput;
use chumsky::prelude::*;
use chumsky::Parser;

use super::super::symbol::SymbolName;
use super::helpers::{self, DecodedOpcode};
use super::{Extra, Span, Tok};

fn canonical_symbol_name(s: &str) -> SymbolName {
    // TODO: avoid copy where possible.
    SymbolName {
        canonical: s
            .chars()
            .filter(|ch: &char| -> bool { *ch != ' ' })
            .collect(),
    }
}

fn is_reserved_identifier(ident: &str, mapper: &helpers::OpcodeMapper) -> bool {
    let is_opcode = move |s: &str| -> bool { matches!(mapper.get(s), DecodedOpcode::Valid(_)) };
    helpers::is_register_name(ident) || is_opcode(ident)
}

fn concat_strings(mut s: String, next: String) -> String {
    s.push_str(&next);
    s
}

// Compound chars are not supported at the moment, see docs/assembler/index.md.
pub(super) fn symex_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    match script_required {
        Script::Normal => select! {
            Tok::NormalSymexSyllable(name) => name,
        },
        _ => unimplemented!(),
    }
    .labelled("symex syllable")
}

fn parse_symex_non_reserved_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    let opcode_mapper = helpers::OpcodeMapper::default();
    symex_syllable(script_required).try_map(move |syllable, span| {
        if is_reserved_identifier(&syllable, &opcode_mapper) {
            Err(Rich::custom(
                span,
                format!("'{syllable}' is a reserved identifier"),
            ))
        } else {
            Ok(syllable)
        }
    })
}

pub(super) fn parse_multi_syllable_symex<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    parse_symex_non_reserved_syllable(script_required)
        .foldl(symex_syllable(script_required).repeated(), concat_strings)
        .labelled("multi-syllable symex")
}

pub(super) fn parse_symex<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, SymbolName, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        parse_multi_syllable_symex(script_required),
        parse_symex_reserved_syllable(script_required),
    ))
    .map(|s| canonical_symbol_name(&s))
    .labelled("symbol name")
}

pub(super) fn parse_symex_reserved_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    let opcode_mapper = helpers::OpcodeMapper::default();
    symex_syllable(script_required)
        .try_map(move |syllable, span| {
            if is_reserved_identifier(&syllable, &opcode_mapper) {
                Ok(syllable)
            } else {
                Err(Rich::custom(span, "expected reserved syllable".to_string()))
            }
        })
        .labelled("reserved symex")
}
