/// terminal contains all the terminals of the grammar; that is, the
/// lowest-level symbols not defined in terms of anything else in the
/// grammar.
use std::ops::Shl;

use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::*;

use super::super::ast::{
    elevate, elevate_normal, elevate_sub, elevate_super, Elevated, HoldBit, LiteralValue,
};
use super::helpers::{self, Sign};
use super::Extra;
use base::{charset::Script, Unsigned36Bit};

pub(super) fn arrow<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((just("->"), just("\u{2192}"))).ignored()
}

pub(super) fn inline_whitespace<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    chumsky::text::inline_whitespace()
}

pub(super) fn at_glyph<'a, I>(
    script: Script,
    name: &'static str,
) -> impl Parser<'a, I, Elevated<char>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let prefix = match script {
        Script::Normal => "",
        Script::Sub => "sub_",
        Script::Super => "super_",
    };
    let output: Elevated<char> = elevate(
        script,
        match name {
            "dot" => '.',
            _ => {
                // I think this panic is OK because it takes place at the
                // time we construct the parser, so it doesn't depend on
                // user input.
                panic!("unknown glyph name {name}");
            }
        },
    );
    let fullname = format!("@{prefix}{name}@");
    just(fullname).to(output)
}

pub(super) fn dot<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn unicode_dot<'a, I>(script_required: Script) -> impl Parser<'a, I, (), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        match script_required {
            Script::Normal => choice((just('\u{22C5}'), just('\u{00B7}')))
                .ignored()
                .boxed(),
            Script::Super => {
                // Unicode Combining Dot Above ̇followed by space ("̇ ")
                just("\u{0307} ").ignored().boxed()
            }
            Script::Sub => {
                // We avoid using '.' as subscript dot, it's too confusing.
                one_of("\u{22C5}\u{00B7}").ignored().boxed()
            }
        }
    }
    at_glyph(script_required, "dot")
        .ignored()
        .or(unicode_dot(script_required))
        .to('.')
        .labelled(match script_required {
            Script::Super => "superscript dot",
            Script::Sub => "subscript dot",
            Script::Normal => "dot",
        })
}

fn digit<'srcbody, I>(
    script_required: Script,
) -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn superscript_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            just('\u{2070}').to('0'),
            just('\u{00B9}').to('1'),
            just('\u{00B2}').to('2'),
            just('\u{00B3}').to('3'),
            just('\u{2074}').to('4'),
            just('\u{2075}').to('5'),
            just('\u{2076}').to('6'),
            just('\u{2077}').to('7'),
            just('\u{2078}').to('8'),
            just('\u{2079}').to('9'),
        ))
        .labelled("superscript digit")
    }

    fn subscript_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            just('\u{2080}').to('0'),
            just('\u{2081}').to('1'),
            just('\u{2082}').to('2'),
            just('\u{2083}').to('3'),
            just('\u{2084}').to('4'),
            just('\u{2085}').to('5'),
            just('\u{2086}').to('6'),
            just('\u{2087}').to('7'),
            just('\u{2088}').to('8'),
            just('\u{2089}').to('9'),
        ))
        .labelled("subscript digit")
    }

    fn normal_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            just('0'),
            just('1'),
            just('2'),
            just('3'),
            just('4'),
            just('5'),
            just('6'),
            just('7'),
            just('8'),
            just('9'),
        ))
        .labelled("digit")
    }

    match script_required {
        Script::Super => superscript_digit().boxed(),
        Script::Sub => subscript_digit().boxed(),
        Script::Normal => normal_digit().boxed(),
    }
}

pub(super) fn digit1<'srcbody, I>(
    script_required: Script,
) -> impl Parser<'srcbody, I, String, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    digit(script_required)
        .repeated()
        .at_least(1)
        .collect::<String>()
        .labelled(match script_required {
            Script::Super => "superscript digits",
            Script::Sub => "subscript digits",
            Script::Normal => "digits",
        })
}

pub(super) fn plus<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Elevated<Sign>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    match script_required {
        Script::Normal => just('+').to(elevate_normal(Sign::Plus)).boxed(),
        Script::Sub => just('\u{208A}').to(elevate_sub(Sign::Plus)).boxed(),
        Script::Super => just('\u{207A}').to(elevate_super(Sign::Plus)).boxed(),
    }
}

pub(super) fn minus<'srcbody, I>(
    script_required: Script,
) -> impl Parser<'srcbody, I, Elevated<Sign>, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    match script_required {
        Script::Normal => just('-').to(elevate_normal(Sign::Minus)).boxed(),
        Script::Sub => just('-').to(elevate_sub(Sign::Minus)).boxed(),
        Script::Super => just('-').to(elevate_super(Sign::Minus)).boxed(),
    }
}

pub(super) fn nonblank_simple_symex_chars<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    any()
        .filter(|ch| super::helpers::is_nonblank_simple_symex_char(*ch))
        .repeated()
        .at_least(1)
        .collect()
        .labelled("nonblank simple symex character")
}

pub(super) fn opcode<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn valid_opcode(s: &str) -> Result<LiteralValue, ()> {
        if let super::helpers::DecodedOpcode::Valid(opcode) = helpers::opcode_to_num(s) {
            Ok(LiteralValue::from((
                Script::Normal,
                // Bits 24-29 (dec) inclusive in the instruction word
                // represent the opcode, so shift the opcode's value
                // left by 24 decimal.
                Unsigned36Bit::from(opcode)
                    .shl(24)
                    // Some opcodes automatically set the hold
                    // bit, so do that here.
                    .bitor(helpers::opcode_auto_hold_bit(opcode)),
            )))
        } else {
            Err(())
        }
    }

    any()
        .repeated()
        .exactly(3)
        .collect::<String>()
        .try_map(|text, span| {
            valid_opcode(&text)
                .map_err(|_| Rich::custom(span, format!("{text} is not a valid opcode")))
        })
        .labelled("opcode")
}

pub(super) fn metacommand_name<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    just("☛☛").ignore_then(
        one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
            .repeated()
            .at_least(2)
            .collect()
            .labelled("metacommand name"),
    )
}

pub(super) fn hold<'a, I>() -> impl Parser<'a, I, HoldBit, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // Accept either 'h' or ':' signalling the hold bit should be set.
    // The documentation seems to use both, though perhaps ':' is the
    // older usage.
    choice((
        one_of("h:").to(HoldBit::Hold),
        just("\u{0305}h").or(just("ℏ")).to(HoldBit::NotHold),
    ))
}

pub(super) fn equals<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    just("=").ignored()
}

pub(super) fn horizontal_whitespace<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("\t ").ignored()
}

pub(super) fn pipe<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    just('|').ignored()
}

pub(super) fn comment<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + StrInput<'a, char>,
{
    just("**").ignore_then(none_of("\n").repeated().ignored())
}

pub(super) fn end_of_input<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + StrInput<'a, char>,
{
    chumsky::prelude::end()
}
