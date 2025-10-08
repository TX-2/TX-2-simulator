use base::charset::Script;
use chumsky::Parser;
use chumsky::input::ValueInput;
use chumsky::prelude::*;

use super::super::lexer::{DOT_CHAR, DOT_STR};
use super::super::span::Span;
use super::super::symbol::SymbolName;
use super::helpers::{self};
use super::{ExtraWithoutContext, Tok, opcode_code};

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
    helpers::is_register_name(ident) || opcode_code(ident).is_some()
}

// Compound chars are not supported at the moment, see docs/assembler/index.md.
pub(super) fn digits_as_symex<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, (String, Option<char>), ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        Tok::Digits(script, literal) if script == script_required => literal,
    }
    .map(|literal| {
        let maybe_dot: Option<char> = if literal.has_trailing_dot() {
            Some(DOT_CHAR)
        } else {
            None
        };
        (literal.take_digits(), maybe_dot)
    })
}

// Compound chars are not supported at the moment, see docs/assembler/index.md.
pub(super) fn symex_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn append_possible_dot((mut prefix, maybe_dot): (String, Option<char>)) -> String {
        match maybe_dot {
            Some(dot) => {
                prefix.push(dot);
                prefix
            }
            None => prefix,
        }
    }

    let one_dot = just(Tok::Dot(script_required))
        .to(DOT_CHAR)
        .labelled(DOT_STR);

    let maybe_dot = one_dot.clone().or_not();
    let without_dot = select! {
        Tok::SymexSyllable(script, name) if script == script_required => name,
    };

    // The dot is a macro terminator.  So eventually we will need to
    // distinguish two meanings of "X@dot@".  The first being a symex
    // named "X@dot@" and the second being a reference to a macro
    // called X with the dot as its terminator.
    choice((
        without_dot.then(maybe_dot).map(append_possible_dot),
        digits_as_symex(script_required).map(append_possible_dot),
        one_dot.to(super::lexer::DOT_STR.to_string()),
    ))
    .labelled("symex syllable")
}

fn parse_symex_non_reserved_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    symex_syllable(script_required).try_map(move |syllable, span| {
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

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub(super) enum SymexSyllableRule {
    OneOnly,
    Multiple,
}

pub(super) fn parse_multi_syllable_symex<'a: 'b, 'b, I>(
    rule: SymexSyllableRule,
    script_required: Script,
) -> Boxed<'a, 'b, I, String, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    // Pass by value here is harmless and simplifies the foldl below.
    #[allow(clippy::needless_pass_by_value)]
    fn concat_strings(mut s: String, next: String) -> String {
        s.push_str(&next);
        s
    }

    match rule {
        SymexSyllableRule::OneOnly => symex_syllable(script_required)
            .labelled("single-syllable symex")
            .boxed(),
        SymexSyllableRule::Multiple => parse_symex_non_reserved_syllable(script_required)
            .foldl(symex_syllable(script_required).repeated(), concat_strings)
            .labelled("multi-syllable symex")
            .boxed(),
    }
}

pub(super) fn parse_symex<'a, I>(
    rule: SymexSyllableRule,
    script_required: Script,
) -> impl Parser<'a, I, SymbolName, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        parse_multi_syllable_symex(rule, script_required),
        parse_symex_reserved_syllable(script_required),
    ))
    .map(|s| canonical_symbol_name(&s))
    .labelled("symbol name")
}

pub(super) fn parse_symex_reserved_syllable<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = SimpleSpan> + ValueInput<'a>,
{
    symex_syllable(script_required)
        .try_map(move |syllable, span| {
            if is_reserved_identifier(&syllable) {
                Ok(syllable)
            } else {
                Err(Rich::custom(span, "expected reserved syllable".to_string()))
            }
        })
        .labelled("reserved symex")
}
