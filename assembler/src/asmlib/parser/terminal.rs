/// terminal contains all the terminals of the grammar; that is, the
/// lowest-level symbols not defined in terms of anything else in the
/// grammar.
use std::ops::Shl;

use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::*;

use super::super::ast::{Elevation, HoldBit, LiteralValue};
use super::helpers;
use super::Extra;
use base::Unsigned36Bit;

pub(super) fn arrow<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((just("->"), just("\u{2192}"))).ignored()
}

pub(super) fn sign<'a, I>() -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("+-")
}

pub(super) fn inline_whitespace<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    chumsky::text::inline_whitespace()
}

pub(super) fn digits1<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    chumsky::text::digits(10).at_least(1).collect::<String>()
}

pub(super) fn dot<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("\u{22C5}\u{00B7}").ignored()
}

pub(super) fn superscript_oct_digit1<'srcbody, I>(
) -> impl Parser<'srcbody, I, String, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn superscript_oct_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        any().filter(|ch| super::helpers::superscript_oct_digit_to_value(*ch).is_some())
    }

    superscript_oct_digit()
        .repeated()
        .at_least(1)
        .collect::<String>()
        .labelled("superscript octal digits")
}

pub(super) fn superscript_dot<'srcbody, I>(
) -> impl Parser<'srcbody, I, &'srcbody str, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    just(
        "\u{0307} ", // Unicode Combining Dot Above ̇followed by space ("̇ ")
    )
}

pub(super) fn superscript_sign<'srcbody, I>(
) -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    one_of(concat!(
        "\u{207B}", // U+207B: superscript minus
        "\u{207A}", // U+207A: superscript plus
    ))
}

pub(super) fn subscript_sign<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    one_of(concat!(
        "\u{208B}", // u+208B: subscript minus
        "\u{208A}", // U+208A: subscript plus
    ))
}
pub(super) fn subscript_oct_digit<'srcbody, I>(
) -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn is_subscript_oct_digit(ch: &char) -> bool {
        super::helpers::subscript_oct_digit_to_value(*ch).is_some()
    }

    any().filter(is_subscript_oct_digit)
}

pub(super) fn subscript_dot<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    just('.')
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
                Elevation::Normal,
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

pub(super) fn double_hand<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let hand = just('☛');
    hand.ignored()
        .then(hand)
        .ignored()
        .labelled("double meta hand")
}

pub(super) fn punch<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // TODO: this is not actually a very good terminal because
    // it lacks context.  For example this is a valid program:
    //
    // 100| 4
    //      PUNCH = 6
    // ☛☛PUNCH 200
    //
    // Here, PUNCH is a perfectly good symbol.
    just("PUNCH").ignored()
}

pub(super) fn decimal<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // TODO: this is not actually a very good terminal for the same reason as PUNCH.
    choice((just("DECIMAL"), just("DEC"))).ignored()
}

pub(super) fn octal<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // TODO: this is not actually a very good terminal for the same reason as PUNCH.
    choice((just("OCTAL"), just("OCT"))).ignored()
}

pub(super) fn hold<'a, I>() -> impl Parser<'a, I, HoldBit, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // Accept either 'h' or ':' signalling the hold bit should be set.
    // The documentation seems to use both, though perhaps ':' is the
    // older usage.
    let h = one_of("h:").to(HoldBit::Hold);
    let nh = just("\u{0305}h").or(just("ℏ")).to(HoldBit::NotHold);
    choice((h, nh))
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
