/// terminal contains all the terminals of the grammar; that is, the
/// lowest-level symbols not defined in terms of anything else in the
/// grammar.
use std::ops::Shl;

use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::*;

use super::super::ast::{
    elevate_normal, elevate_sub, elevate_super, Elevated, HoldBit, LiteralValue,
};
use super::helpers::{self, Sign};
use super::{Extra, Span};
use base::{charset::Script, Unsigned36Bit};

pub(super) fn arrow<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((
        just("->").ignored().boxed(),
        just("\u{2192}").ignored().boxed(),
        at_glyph(Script::Normal, "arr").ignored().boxed(),
    ))
    .labelled("arrow")
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
) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let prefix = match script {
        Script::Normal => "",
        Script::Sub => "sub_",
        Script::Super => "super_",
    };
    let output: char = match name {
        "dot" => '\u{00B7}', // centre dot, not full-stop.
        "i" => 'i',
        "j" => 'j',
        "k" => 'k',
        "n" => 'n',
        "p" => 'p',
        "q" => 'q',
        "t" => 't',
        "w" => 'w',
        "x" => 'x',
        "y" => 'y',
        "z" => 'z',
        "underscore" => '_',
        "square" => '\u{25A1}', // Unicode white square,
        "circle" => '\u{25CB}', // Unicode white circle,
        "A" => 'A',
        "B" => 'B',
        "C" => 'C',
        "D" => 'D',
        "E" => 'E',
        "F" => 'F',
        "G" => 'G',
        "H" => 'H',
        "I" => 'I',
        "J" => 'J',
        "K" => 'K',
        "L" => 'L',
        "M" => 'M',
        "N" => 'N',
        "O" => 'O',
        "P" => 'P',
        "Q" => 'Q',
        "R" => 'R',
        "S" => 'S',
        "T" => 'T',
        "U" => 'U',
        "V" => 'V',
        "W" => 'W',
        "X" => 'X',
        "Y" => 'Y',
        "Z" => 'Z',
        "alpha" => 'α',
        "beta" => 'β',
        "gamma" => 'γ',
        "delta" => 'Δ',
        "eps" => 'ε', // epsilon
        "lambda" => 'λ',
        "apostrophe" => '\'',
        "0" => '0',
        "1" => '1',
        "2" => '2',
        "3" => '3',
        "4" => '4',
        "5" => '5',
        "6" => '6',
        "7" => '7',
        "8" => '8',
        "9" => '9',
        "?" => '?', // usually denotes a trasncription problem.
        "+" => '+',
        "hamb" => '≡', // "identical to" but perhaps we should also accept (on input) ☰ (U+2630, Trigram For Heaven).
        "times" => '×',
        "arr" => '\u{2192}',
        "minus" => '-',
        "hand" => '☛',
        "pipe" => '|',
        "rect_dash" => '\u{25A3}',
        "circled_v" => '\u{24CB}',
        "sup" => '\u{2283}',
        _ => {
            // I think this panic is OK because it takes place at the
            // time we construct the parser, so it doesn't depend on,
            // user input.
            panic!("unknown glyph name {name}");
        }
    };
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
        .to('\u{00B7}') // centre dot, not "."
        .labelled(match script_required {
            Script::Super => "superscript dot",
            Script::Sub => "subscript dot",
            Script::Normal => "dot",
        })
}

pub(crate) fn digit<'srcbody, I>(
    script_required: Script,
) -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn superscript_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        one_of("\u{2070}\u{00B9}\u{00B2}\u{00B3}\u{2074}\u{2075}\u{2076}\u{2077}\u{2078}\u{2079}")
            .map(|ch| {
                helpers::convert_superscript_digit(ch)
                    .expect("only superscript digits should be passed")
            })
            .labelled("superscript digit")
    }

    fn subscript_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        one_of("\u{2080}\u{2081}\u{2082}\u{2083}\u{2084}\u{2085}\u{2086}\u{2087}\u{2088}\u{2089}")
            .map(|ch| {
                helpers::convert_subcript_digit(ch).expect("only subscript digits should be passed")
            })
            .labelled("subscript digit")
    }

    fn normal_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        one_of("0123456789").labelled("digit")
    }

    fn digit_glyph<'srcbody, I>(
        script_required: Script,
    ) -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            at_glyph(script_required, "0"),
            at_glyph(script_required, "1"),
            at_glyph(script_required, "2"),
            at_glyph(script_required, "3"),
            at_glyph(script_required, "4"),
            at_glyph(script_required, "5"),
            at_glyph(script_required, "6"),
            at_glyph(script_required, "7"),
            at_glyph(script_required, "8"),
            at_glyph(script_required, "9"),
        ))
    }

    choice((
        digit_glyph(script_required),
        match script_required {
            Script::Super => superscript_digit().boxed(),
            Script::Sub => subscript_digit().boxed(),
            Script::Normal => normal_digit().boxed(),
        },
    ))
    .labelled("digit")
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
        Script::Sub => at_glyph(Script::Sub, "+")
            .or(just('\u{208A}'))
            .to(elevate_sub(Sign::Plus))
            .boxed(),
        Script::Super => at_glyph(Script::Super, "+")
            .or(just('\u{207A}'))
            .to(elevate_super(Sign::Plus))
            .boxed(),
    }
}

pub(super) fn minus<'srcbody, I>(
    script_required: Script,
) -> impl Parser<'srcbody, I, Sign, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    let glyph = at_glyph(script_required, "minus");
    match script_required {
        Script::Normal => just('-').or(glyph).boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
    .to(Sign::Minus)
}

fn lw_lowercase_letter_except_h<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn lowercase_letter_glyph<'a, I>(
        script_required: Script,
    ) -> impl Parser<'a, I, char, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((
            // h is deliberately missing; it is not allowed in a
            // symex.
            at_glyph(script_required, "i"),
            at_glyph(script_required, "j"),
            at_glyph(script_required, "k"),
            at_glyph(script_required, "n"),
            at_glyph(script_required, "p"),
            at_glyph(script_required, "q"),
            at_glyph(script_required, "t"),
            at_glyph(script_required, "w"),
            at_glyph(script_required, "x"),
            at_glyph(script_required, "y"),
            at_glyph(script_required, "z"),
        ))
    }

    match script_required {
        Script::Normal => lowercase_letter_glyph(script_required)
            .or(one_of("ijknpqtwxyz"))
            .boxed(),
        Script::Sub | Script::Super => lowercase_letter_glyph(script_required).boxed(),
    }
    .labelled(match script_required {
        Script::Normal => "lowercase letter",
        Script::Sub => "subscript lowercase letter",
        Script::Super => "superscript lowercase letter",
    })
}

fn lw_greek_letter<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn lw_greek_letter_glyph<'a, I>(
        script_required: Script,
    ) -> impl Parser<'a, I, char, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((
            at_glyph(script_required, "alpha"),
            at_glyph(script_required, "beta"),
            at_glyph(script_required, "gamma"),
            at_glyph(script_required, "delta"),
            at_glyph(script_required, "eps"),
            at_glyph(script_required, "lambda"),
        ))
    }

    match script_required {
        Script::Sub | Script::Super => lw_greek_letter_glyph(script_required).boxed(),
        Script::Normal => lw_greek_letter_glyph(script_required)
            .or(one_of(concat!(
                "α", // Greek small letter alpha, U+03B1
                "β", // Greek beta symbol, U+03B2
                "γ", // Greek small letter gamma (U+03B3)
                "Δ", // Greek capital delta, U+0394
                "ε", // Greek small letter epsilon, U+03B5
                "λ", // Greek small letter lambda, U+03BB
            )))
            .boxed(),
    }
}

fn uppercase_letter<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn uppercase_letter_glyph<'a, I>(
        script_required: Script,
    ) -> impl Parser<'a, I, char, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((
            at_glyph(script_required, "A"),
            at_glyph(script_required, "B"),
            at_glyph(script_required, "C"),
            at_glyph(script_required, "D"),
            at_glyph(script_required, "E"),
            at_glyph(script_required, "F"),
            at_glyph(script_required, "G"),
            at_glyph(script_required, "H"),
            at_glyph(script_required, "I"),
            at_glyph(script_required, "J"),
            at_glyph(script_required, "K"),
            at_glyph(script_required, "L"),
            at_glyph(script_required, "M"),
            at_glyph(script_required, "N"),
            at_glyph(script_required, "O"),
            at_glyph(script_required, "P"),
            at_glyph(script_required, "Q"),
            at_glyph(script_required, "R"),
            at_glyph(script_required, "S"),
            at_glyph(script_required, "T"),
            at_glyph(script_required, "U"),
            at_glyph(script_required, "V"),
            at_glyph(script_required, "W"),
            at_glyph(script_required, "X"),
            at_glyph(script_required, "Y"),
            at_glyph(script_required, "Z"),
        ))
    }

    match script_required {
        Script::Normal => uppercase_letter_glyph(Script::Normal)
            .or(one_of("ABCDEFGHIJKLMNOPQRSTUVWXYZ"))
            .boxed()
            .labelled("uppercase letter"),
        Script::Super => {
            uppercase_letter_glyph(Script::Super)
                .boxed()
                .or(choice((
                    just('ᴬ').to('A'),
                    just('ᴮ').to('B'),
                    just('\u{A7F2}').to('C'),
                    just('ᴰ').to('D'),
                    just('ᴱ').to('E'),
                    just('\u{A7F3}').to('F'),
                    just('ᴳ').to('G'),
                    just('ᴴ').to('H'),
                    just('ᴵ').to('I'),
                    just('ᴶ').to('J'),
                    just('ᴷ').to('K'),
                    just('ᴸ').to('L'),
                    just('ᴹ').to('M'),
                    just('ᴺ').to('N'),
                    just('ᴼ').to('O'),
                    just('ᴾ').to('P'),
                    just('\u{A7F4}').to('Q'),
                    just('ᴿ').to('R'),
                    just('\u{209B}').to('S'),
                    just('ᵀ').to('T'),
                    just('ᵁ').to('U'),
                    just('ⱽ').to('V'),
                    just('ᵂ').to('W'),
                    just('\u{2093}').to('X'),
                    // No superscript Y, Z.
                )))
                .boxed()
                .labelled("superscript uppercase letter")
        }
        Script::Sub => uppercase_letter_glyph(Script::Sub)
            .boxed()
            .labelled("subscript uppercase letter"),
    }
}

fn underscore<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let glyph = at_glyph(script_required, "underscore");

    match script_required {
        Script::Normal => just('_').or(glyph).boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
}

fn overbar<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let glyph = at_glyph(script_required, "underscore");

    match script_required {
        Script::Normal => glyph
            .or(just(
                '\u{203E}', // Unicode non-combining overline,
            ))
            .boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
}

fn square<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let glyph = at_glyph(script_required, "square");

    match script_required {
        Script::Normal => glyph
            .or(just(
                '\u{25A1}', // Unicode white square,
            ))
            .boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
}

fn circle<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let glyph = at_glyph(script_required, "circle");

    match script_required {
        Script::Normal => glyph
            .or(just(
                '\u{25CB}', // Unicode white circle
            ))
            .boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
}

fn apostrophe<'a, I>(script_required: Script) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let glyph = at_glyph(script_required, "apostrophe");
    match script_required {
        Script::Normal => glyph.or(just('\'')).boxed(),
        Script::Sub | Script::Super => glyph.boxed(),
    }
}

fn nonblank_simple_symex_char<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, char, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((
        digit(script_required).boxed(),
        uppercase_letter(script_required).boxed(),
        lw_greek_letter(script_required).boxed(),
        lw_lowercase_letter_except_h(script_required).boxed(),
        dot(script_required).boxed(),
        apostrophe(script_required).boxed(),
        underscore(script_required).boxed(),
        overbar(script_required).boxed(),
        square(script_required).boxed(),
        circle(script_required).boxed(),
        // Although space is valid inside a symex, we handle that
        // elsewhere.
    ))
    .labelled("nonblank simple symex character")
}

pub(super) fn nonblank_simple_symex_chars<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    nonblank_simple_symex_char(script_required)
        .repeated()
        .at_least(1)
        .collect()
}

pub(super) fn opcode<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn valid_opcode(span: Span, s: &str) -> Result<LiteralValue, ()> {
        if let super::helpers::DecodedOpcode::Valid(opcode) = helpers::opcode_to_num(s) {
            Ok(LiteralValue::from((
                span,
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
            valid_opcode(span, &text)
                .map_err(|_| Rich::custom(span, format!("{text} is not a valid opcode")))
        })
        .labelled("opcode")
}

pub(super) fn metacommand_name<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    pub(super) fn hand<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        at_glyph(Script::Normal, "hand").or(just('☛')).ignored()
    }

    pub(super) fn doublehand<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        hand().then(hand()).ignored()
    }

    doublehand().ignore_then(
        uppercase_letter(Script::Normal)
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

pub(super) fn opt_horizontal_whitespace<'srcbody, I>(
) -> impl Parser<'srcbody, I, (), Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + StrInput<'srcbody, char>,
{
    horizontal_whitespace().or_not().ignored()
}

pub(super) fn horizontal_whitespace<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("\t ").repeated().at_least(1).ignored()
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
