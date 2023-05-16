use base::charset::Script;
use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::*;
use chumsky::Parser;

use super::super::symbol::SymbolName;
use super::helpers::{self, DecodedOpcode};
use super::terminal;
use super::Extra;

fn canonical_symbol_name(s: &str) -> SymbolName {
    // TODO: avoid copy where possible.
    SymbolName {
        canonical: s
            .chars()
            .filter(|ch: &char| -> bool { *ch != ' ' })
            .collect(),
    }
}

fn is_reserved_identifier(ident: &str) -> bool {
    helpers::is_register_name(ident)
        || matches!(helpers::opcode_to_num(ident), DecodedOpcode::Valid(_))
}

fn concat_strings(mut s: String, next: String) -> String {
    s.push_str(&next);
    s
}

// Compound chars are not supported at the moment, see docs/assembler/index.md.
fn symex_syllable<'a, I>(script_required: Script) -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    terminal::nonblank_simple_symex_chars(script_required).labelled("symex syllable")
}

fn parse_symex_non_reserved_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    symex_syllable(script_required).try_map(|syllable, span| {
        if is_reserved_identifier(&syllable) {
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
) -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    parse_symex_non_reserved_syllable(script_required)
        .foldl(
            symex_syllable(script_required)
                .padded_by(terminal::horizontal_whitespace0())
                .repeated(),
            concat_strings,
        )
        .labelled("multi-syllable symex")
}

pub(super) fn parse_symex<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, SymbolName, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
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
) -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    symex_syllable(script_required)
        .try_map(|syllable, span| {
            if is_reserved_identifier(&syllable) {
                Ok(syllable)
            } else {
                Err(Rich::custom(span, "expected reserved syllable".to_string()))
            }
        })
        .labelled("reserved symex")
}
