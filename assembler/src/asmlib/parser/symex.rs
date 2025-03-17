use base::charset::Script;
use chumsky::input::ValueInput;
use chumsky::prelude::*;
use chumsky::Parser;

use super::super::lexer::{NumericLiteral, DOT_CHAR, DOT_STR};
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
pub(super) fn digits_as_symex<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, (String, Option<char>), Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn accept(literal: &NumericLiteral) -> bool {
        literal.sign().is_none()
    }

    let digits_as_symex = match script_required {
        Script::Normal => select! {
            Tok::NormalDigits(literal) if accept(&literal) => literal,
        }
        .boxed(),
        Script::Super => select! {
            Tok::SuperscriptDigits(literal) if accept(&literal) => literal,
        }
        .boxed(),
        Script::Sub => select! {
            Tok::SubscriptDigits(literal) if accept(&literal) => literal,
        }
        .boxed(),
    };

    digits_as_symex.map(|literal| {
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
) -> impl Parser<'a, I, String, Extra<'a>> + Clone
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
    let without_dot = match script_required {
        Script::Normal => select! {
            Tok::NormalSymexSyllable(name) => name,
        }
        .boxed(),
        Script::Super => select! {
            Tok::SuperscriptSymexSyllable(name) => name,
        }
        .boxed(),
        Script::Sub => select! {
            Tok::SubscriptSymexSyllable(name) => name,
        }
        .boxed(),
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
