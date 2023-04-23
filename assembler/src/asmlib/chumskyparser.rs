// This code is not yet used, but I don't want to comment things out
// or ass cfg conditionals as I will simply need to reverse them when
// we do start using it.
#![allow(unused_imports)]
#![allow(dead_code)]

mod helpers;
#[cfg(test)]
mod tests; // temporary

use std::ops::Shl;

use chumsky::error::Rich;
use chumsky::extra::Full;
use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::*;
use chumsky::primitive::one_of;
use chumsky::text::{digits, inline_whitespace};
use chumsky::Parser;

use super::ast::*;

use super::state::NumeralMode;
use super::types::*;
use base::prelude::*;

//use helpers::*;

#[derive(Debug, Clone)]
pub(crate) struct ErrorLocation {
    /// line is usually derived from LocatedSpan::location_line() which returns
    /// a u32.
    pub(crate) line: LineNumber,
    pub(crate) column: Option<usize>,
}

pub(crate) type Extra<'a, T> = Full<Rich<'a, T>, NumeralMode, ()>;

fn opt_sign<'a, I>() -> impl Parser<'a, I, Option<char>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("+-").or_not().labelled("sign")
}

fn digits1<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    digits(10).at_least(1).collect::<String>()
}

fn maybe_dot<'a, I>() -> impl Parser<'a, I, bool, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    one_of("\u{22C5}\u{00B7}").or_not().map(|x| x.is_some())
}

fn normal_literal<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    opt_sign()
        .then(digits1())
        .then(maybe_dot())
        .try_map_with_state(|((maybe_sign, digits), hasdot), span, state| {
            match helpers::make_num(maybe_sign, &digits, hasdot, state) {
                Ok(value) => Ok(LiteralValue::from((Elevation::Normal, value))),
                Err(e) => Err(Rich::custom(span, e.to_string())),
            }
        })
        .labelled("numeric literal")
}

//) -> impl Parser<'srcbody, &'srcbody str, LiteralValue, Extra<'srcbody, I>> {
//    let maybe_sign = one_of("-+").or_not();
//    // Accept either Unicode Dot Operator U+22C5 ("⋅") or Unicode Middle Dot U+00B7 ("·").
//    let maybe_dot = one_of("\u{22C5}\u{00B7}").or_not();
//    let digits1 = digits(10).at_least(1).slice();
//    let normal_number =
//        opt_sign
//            .then(digits1)
//            .then(maybe_dot)
//            .map_with_state(|output, _span, state| {
//                let sign: Option<char> = output.0 .0;
//                let digits = output.0 .1;
//                let hasdot = output.1 .0;
//                helpers::make_num(sign, digits, state, hasdot)
//            });
//    normal_number.map(|n| InstructionFragment {
//        elevation: Elevation::Normal,
//        value: n,
//    })
//}

fn superscript_oct_digit1<'srcbody, I>() -> impl Parser<'srcbody, I, String, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn superscript_oct_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        any().filter(|ch| helpers::superscript_oct_digit_to_value(*ch).is_some())
    }

    superscript_oct_digit()
        .repeated()
        .at_least(1)
        .collect::<String>()
}

fn maybe_superscript_dot<'srcbody, I>() -> impl Parser<'srcbody, I, bool, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    just(
        "\u{0307} ", // Unicode Combining Dot Above ̇followed by space ("̇ ")
    )
    .or_not()
    .map(|x| x.is_some())
}

fn superscript_literal<'srcbody, I>(
) -> impl Parser<'srcbody, I, LiteralValue, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn maybe_superscript_sign<'srcbody, I>(
    ) -> impl Parser<'srcbody, I, Option<char>, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        one_of(concat!(
            "\u{207B}", // U+207B: superscript minus
            "\u{207A}", // U+207A: superscript plus
        ))
        .or_not()
    }

    maybe_superscript_sign()
        .then(superscript_oct_digit1())
        .then(maybe_superscript_dot())
        .try_map_with_state(|((maybe_sign, digits), hasdot), span, state| {
            match helpers::make_superscript_num(maybe_sign, &digits, hasdot, state) {
                Ok(value) => Ok(LiteralValue::from((Elevation::Superscript, value))),
                Err(e) => Err(Rich::custom(span, e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn subscript_literal<'srcbody, I>() -> impl Parser<'srcbody, I, LiteralValue, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn is_subscript_oct_digit(ch: &char) -> bool {
        helpers::subscript_oct_digit_to_value(*ch).is_some()
    }

    fn maybe_subscript_sign<'srcbody, I>(
    ) -> impl Parser<'srcbody, I, Option<char>, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        one_of(concat!(
            "\u{208B}", // u+208B: subscript minus
            "\u{208A}", // U+208A: subscript plus
        ))
        .or_not()
    }

    fn subscript_oct_digit<'srcbody, I>() -> impl Parser<'srcbody, I, char, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        any().filter(is_subscript_oct_digit)
    }
    fn subscript_oct_digit1<'srcbody, I>() -> impl Parser<'srcbody, I, String, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        subscript_oct_digit()
            .repeated()
            .at_least(1)
            .collect::<String>()
    }

    /// Recognise a subscript dot.  On the Linconln Writer, the dot
    /// is raised above the line, like the dot customarily used for
    /// the dot-product.  Hence for subscripts we use the regular
    /// ascii dot (full stop, period) which is on the line.
    fn maybe_subscript_dot<'srcbody, I>() -> impl Parser<'srcbody, I, bool, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        just('.').or_not().map(|x| x.is_some())
    }
    maybe_subscript_sign()
        .then(subscript_oct_digit1())
        .then(maybe_subscript_dot())
        .try_map_with_state(|((maybe_sign, digits), hasdot), span, state| {
            match helpers::make_subscript_num(maybe_sign, &digits, hasdot, state) {
                Ok(value) => Ok(LiteralValue::from((Elevation::Subscript, value))),
                Err(e) => Err(Rich::custom(span, e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn program_instruction_fragment<'srcbody, I>(
) -> impl Parser<'srcbody, I, InstructionFragment, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + StrInput<'srcbody, char>,
{
    //inline_whitespace().ignore_then(expression().map(InstructionFragment::from))
    inline_whitespace().ignore_then(
        literal().map(|literal| InstructionFragment::from(Expression::Literal(literal))),
    )
}

fn spaces1<'srcbody, I>() -> impl Parser<'srcbody, I, (), Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    just(' ').repeated().at_least(1).ignored()
}

mod symex {
    use chumsky::input::ValueInput;
    use chumsky::prelude::*;
    use chumsky::primitive::just;
    use chumsky::text::{digits, inline_whitespace};
    use chumsky::Parser;

    use super::super::ast::{Elevation, LiteralValue};
    use super::helpers::{self, is_nonblank_simple_symex_char, DecodedOpcode};
    use super::{spaces1, Extra, SymbolName};
    use base::Unsigned36Bit;

    /// Recognise a single dead character, a character which does not
    /// advance the character/cursor when printed.
    pub(crate) fn dead_char<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        one_of(concat!(
            "\u{0332}", // combining low line
            "\u{0305}", // combining overline
            "\u{20DD}", // combining enclosing circle
            "\u{20DE}", // combining enclosing square
        ))
        .map(|ch| [ch].into_iter().collect())
    }

    fn canonical_symbol_name(s: &str) -> SymbolName {
        // TODO: avoid copy where possible.
        SymbolName {
            canonical: s
                .chars()
                .filter(|ch: &char| -> bool { *ch != ' ' })
                .collect(),
        }
    }

    ////    /// Recognise a single compound character.
    ////    ///
    ////    /// ## Users Handbook Definition of Compound Characters
    ////    ///
    ////    /// Compound chars are described in item 7 on page 607 of the TX-2
    ////    /// Users Handbook (Nov 63).
    ////    ///
    ////    /// Compound characters are described like so:
    ////    ///
    ////    ///  - Only one backspace
    ////    ///  - Two or three characters only.
    ////    ///  - Space bar is allowed
    ////    ///  - Any sequence of characters is legal. (Except ...)
    ////    ///
    ////    /// This seems confusing at first but the key to understanding
    ////    /// it is that the Lincoln Writer (from which these characters
    ////    /// come) has four characters which don't advance the carriage
    ////    /// when they are printed (underline, overline, square,
    ////    /// circle).  That is, the following character is overstruck.
    ////    /// The underline _ is one such character: then _ followed by G
    ////    /// is a compound character, _ overstruck with G.  This would
    ////    /// be a two-character compound character.
    ////    ///
    ////    /// A compound character can also be formed with a space,
    ////    /// presumably for example a character which doesn't advance
    ////    /// the carriage followed by a space, which does.
    ////    ///
    ////    /// Using our single allowed backspace, we could create a
    ////    /// compound character using a character which does advance the
    ////    /// carriage, for example K.  K\b> K overstruck with a >.
    ////    ///
    ////    /// Another three-character option is to use two
    ////    /// non-carriage-advancing characters.  The documentation
    ////    /// doesn't seem to clearly state whether Lincoln Writer codes
    ////    /// 0o74 and 0o75 ("LOWER CASE" and "UPPER CASE") are
    ////    /// permitted.  This makes a difference because for example
    ////    /// CIRCLE is upper case while SQUARE is lower case (both
    ////    /// signaled by code 013).   So I am not clear on whether
    ////    /// this sequence of codes is a valid single compound
    ////    /// character (assume we start in upper-case).
    ////    ///
    ////    /// Code  Representing          Advances carriage?
    ////    /// 013   CIRCLE                No (it's special)
    ////    /// 074   Shift to lower case   No (it's non-printing)
    ////    /// 013   SQUARE                No (it's special)
    ////    /// 057   *                     Yes (rightward)
    ////    ///
    ////    /// If valid this would represent a circle, square and asterisk
    ////    /// all on the same spot.
    ////    ///
    ////    /// For the moment we don't need to worry about this, because we
    ////    /// cannot tell the difference; the current parser implementation
    ////    /// accepts Unicode input, and by the time the Lincoln Writer code
    ////    /// have been translated into Unicode, the upper/lower case shift
    ////    /// codes are no longer present in the parser's input.
    ////    ///
    ////    /// Another input that tests our understanding is this one:
    ////    ///
    ////    /// Code  Representing          Advances carriage?
    ////    /// 013   CIRCLE                No (it's special)
    ////    /// 062   Backspace             Yes (leftward!)
    ////    /// 012   _ (underline)         No (it's special)
    ////    ///
    ////    /// This meets the letter of the condition (just one backspace,
    ////    /// only three characters).  But the net effect of these code is a
    ////    /// net leftward movement of the carriage/cursor.
    ////    ///
    ////    /// Yet another:
    ////    /// 031   J                     Yes
    ////    /// 062   Backspace             Yes (leftward!)
    ////    /// 027   H                     Yes
    ////    /// 062   Backspace             Yes (leftward!)
    ////    /// 032   K                     Yes
    ////    ///
    ////    /// Here we apparently see 031 062 027 as the first compound
    ////    /// character (three characters, one backspace) but is the
    ////    /// following thing valid?  The problem is it starts with a
    ////    /// backspace.  That cannot be part of the initial compound
    ////    /// character because only one backspace is allowed.
    ////    ///
    ////    /// ## Additional Restrictions
    ////    ///
    ////    /// It seems that the Users Handbook underspecifies the compound
    ////    /// character.  We will have to do something - accept some inputs
    ////    /// and perhaps reject others.
    ////    ///
    ////    /// For now, I plan to add additional restrictions, not stated in
    ////    /// the Users Handbook, which helps disambiguate:
    ////    ///
    ////    /// A compound character is a sequene of two or three characters
    ////    /// which
    ////    ///  1. Does not begin with a backspace
    ////    ///  2. Does not end with a backspace
    ////    ///  3. Does not end with a dead character (a character which does
    ////    ///     not advance the carriage).
    ////    ///  4. Includes either a backspace or a dead character.
    ////    ///
    ////    /// The thinking behind this restriction is that it enforces a
    ////    /// requirement that the "compound character" not overlap with
    ////    /// those characters that precede or follow it.
    ////    ///
    ////    /// If D represents a non-advancing character (_, square, and so
    ////    /// on), X represents a character which does advance the carriage,
    ////    /// S represents space and \b represents backspace, these are
    ////    /// valid compound characters:
    ////    ///
    ////    /// DS
    ////    /// DX
    ////    /// S\bX
    ////    /// X\bS
    ////    /// S\bS (more about this one below)
    ////    /// DDS
    ////    /// DDX
    ////    ///
    ////    /// In terms of error-handling, once we see a dead character at
    ////    /// the current input position, we know that we need to end up
    ////    /// with a compound character which starts with it.  Once we see a
    ////    /// regular character which advances the carriage followed by a
    ////    /// backspace, we know we must be looking at a three-character
    ////    /// compound character (i.e. it's an error for the character after
    ////    /// the \b to be a dead character).
    ////    ///
    ////    /// The following examples would not be valid because the above
    ////    /// rule disallows them.  After each I identify in parentheses the
    ////    /// reason I think it should not be allowed (i.e. why our
    ////    /// additional restriction is helpful).
    ////    ///
    ////    /// XX\b (would overlap the next character)
    ////    /// DDD  (would overlap the next character)
    ////    /// DXD  (would overlap the next character)
    ////    /// DSD  (would overlap the next character)
    ////    /// DDD  (would overlap the next character)
    ////    /// SDD  (would overlap the next character)
    ////    /// XDD  (would overlap the next character)
    ////    /// \bDX (would overlap the previous character)
    ////    /// \bXX (similar, but also visually appears to be two characters).
    ////    ///
    ////    /// These rules permit the form "S\bS" even though that's
    ////    /// potentially confusing for users in that it is visually
    ////    /// insidtinguishable from a single space.
    ////    ///
    ////    /// Condition 4 above ensures that these forms are not considered
    ////    /// compound characters:
    ////    ///
    ////    /// XX  (we want to parse that as two simple characters)
    ////    /// XXX (we want to parse that as three simple characters)
    ////    /// XSX (we want to parse that as two single-character syllables
    ////    ///     separated by a space)
    ////    /// XDX (we want to parse this as the simple character X followed by
    ////    ///      the compound character DX, because this reflects the fact
    ////    ///      that the syllable takes up two "columns")
    ////    ///
    ////    /// This overstriking behaviour is described by A. Vanderburgh
    ////    /// in "The Lincoln Keyboard - a typewriter keyboard designed
    ////    /// for computers imput flexibility", a one-page paper in
    ////    /// Communications of the ACM, Volume 1, Issue 7, July 1958
    ////    /// (https://doi.org/10.1145/368873.368879).
    pub(crate) fn parse_compound_char<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        // accepts a single character which advances the carriage.
        fn advances<'a, I>() -> impl Parser<'a, I, char, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
        {
            fn parse_simple_nonblank<'a, I>() -> impl Parser<'a, I, char, Extra<'a, char>>
            where
                I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
            {
                any().filter(|ch| is_nonblank_simple_symex_char(*ch))
            }
            just(' ').or(parse_simple_nonblank())
        }

        const BACKSPACE: char = '\u{8}';

        fn bs<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
        {
            advances()
                .then(just(BACKSPACE))
                .then(advances())
                .map(|((ch1, ch2), ch3)| [ch1, ch2, ch3].into_iter().collect())
        }

        fn two<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
        {
            dead_char().then(advances()).map(|(mut s, ch)| {
                s.push(ch);
                s
            })
        }

        fn three<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
        {
            bs().or(dead_char().then(two()).map(|(mut s1, s2)| {
                s1.push_str(&s2);
                s1
            }))
        }
        choice((two(), three()))
    }

    fn is_reserved_identifier(ident: &str) -> bool {
        helpers::is_register_name(ident)
            || matches!(helpers::opcode_to_num(ident), DecodedOpcode::Valid(_))
    }

    fn parse_nonblank_simple_symex_chars<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        any()
            .filter(|ch| is_nonblank_simple_symex_char(*ch))
            .repeated()
            .at_least(1)
            .collect()
    }

    fn concat_strings(mut s: String, next: String) -> String {
        s.push_str(&next);
        s
    }

    // This function gives the impression it wouldn't be very
    // efficient, but any TX-2 program will have to fit into the
    // address space of the machine, meaning that the assembler input
    // is unlikely to be more than 2^17 lines.  We can profile the
    // assembler on some longer input once the assembler actually
    // works.  For now we're concerned with correctness and we'll punt
    // on efficiency until we can quantify any problem.
    fn parse_symex_syllable<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        let parsers = || {
            (
                parse_nonblank_simple_symex_chars(), // returns String
                // compound chars containing a space still don't terminate the symex.
                parse_compound_chars(),
            )
        };
        choice(parsers()).foldl(choice(parsers()).repeated(), concat_strings)
    }

    fn parse_compound_chars<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        parse_compound_char().foldl(parse_compound_char().repeated(), concat_strings)
    }

    pub(super) fn parse_symex_reserved_syllable<'a, I>(
    ) -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        parse_symex_syllable().try_map(|syllable, span| {
            if is_reserved_identifier(&syllable) {
                Ok(syllable)
            } else {
                Err(Rich::custom(span, "expected reserved syllable".to_string()))
            }
        })
    }

    fn parse_symex_non_reserved_syllable<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        parse_symex_syllable().try_map(|syllable, span| {
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

    pub(super) fn parse_multi_syllable_symex<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        fn space_syllable<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
        {
            spaces1().ignore_then(parse_symex_syllable())
        }

        parse_symex_non_reserved_syllable()
            .then(
                space_syllable()
                    .repeated()
                    // TODO: find a way to cut down on allocation of temporary strings.
                    .collect::<Vec<String>>()
                    .map(|v| v.join("")),
            )
            .map(|(head, tail)| format!("{head}{tail}"))
    }

    pub(super) fn parse_symex<'a, I>() -> impl Parser<'a, I, SymbolName, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((
            parse_multi_syllable_symex(),
            parse_symex_reserved_syllable(),
        ))
        .map(|s| canonical_symbol_name(&s))
        // TODO: label this.
    }
}

fn literal<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((normal_literal(), superscript_literal(), subscript_literal()))
}

fn opcode<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn valid_opcode(s: &str) -> Result<LiteralValue, ()> {
        if let helpers::DecodedOpcode::Valid(opcode) = helpers::opcode_to_num(s) {
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

////// Parse an expression; these can currently only take the form of a literal.
////// TX-2's M4 assembler allows arithmetic expressions also, but these are not
////// currently implemented.
//////
////// When we do implement fuller support for expressions, we need to pay
////// attention to the rules for symex termination (see section 6-2.3
////// "RULES FOR SYMEX FORMATION" item 8), because script changes
////// terminate symexes.
//////
////// This means that BAT² is not an identifier but a sequence[1] whose
////// value is computed by OR-ing the value of the symex BAT with the
////// value of the literal "²" (which is 2<<30, or 0o20_000_000_000).
////// Whether BAT² is itself an expression or an "InstructionFragment" is
////// something we will need to consider carefully.  For example, is
////// (BAT²) valid?  If yes, then so is (BAT²)+1, meaning that our
////// current rule for instruction_fragment may have to change
////// significantly.
//////
////// [1] I use "sequence" in the paragraph above to avoid saying
////// "expression" or "instruction fragment".
////fn expression<'a, I>() -> impl Parser<'a, I, Expression, Extra<'a, char>>
////where
////    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
////{
////    fn symbolic_expression<'srcbody, I: Input<'srcbody>>(
////    ) -> impl Parser<'srcbody, &'srcbody str, Expression, Extra<'srcbody, I>> {
////        symbol().map(|name| Expression::Symbol(Elevation::Normal, name))
////    }
////
////    fn literal_expression<'srcbody, I: Input<'srcbody>>(
////    ) -> impl Parser<'srcbody, &'srcbody str, Expression, Extra<'srcbody, I>> {
////        choice((literal(), opcode())).map(Expression::from)
////    }
////
////    choice((literal_expression(), symbolic_expression()))
////}

////
/////// An address expression is a literal value or a symex.  That is I
/////// think it's not required that an arithmetic expression
/////// (e.g. "5+BAR") be accepted in an origin notation (such as
/////// "<something>|").
////fn address_expression<'srcbody, I: Input<'srcbody>>(
////) -> impl Parser<'srcbody, &'srcbody str, Address, Extra<'srcbody, I>> {
////    // We should eventually support symexes here.
////    literal.map_res(|literal| Address::try_from(literal.value()))
////}

//// fn symbol<'a, I>() -> impl Parser<'a, I, SymbolName, Extra<'a, char>>
//// where
////     I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
//// {
////     symex::parse_symex()
////         .map(SymbolName::from)
////         .labelled("symex (symbol) name")
//// }

////fn tag_definition<'srcbody, I: Input<'srcbody>>(
////) -> impl Parser<'srcbody, &'srcbody str, SymbolName, Extra<'srcbody, I>> {
////    fn arrow<'srcbody, I: Input<'srcbody>>(
////    ) -> impl Parser<'srcbody, &'srcbody str, (), Extra<'srcbody, I>> {
////        let just_arrow = choice((
////            just("->"),
////            just("\u{2192}"), // Unicode rightwards pointing arrow
////        ));
////        inline_whitespace()
////            .ignore_then(just_arrow())
////            .ignore_then(inline_whitespace())
////            .ignored()
////    }
////
////    symbol().then_ignore(arrow())
////}
////
////#[cfg(notyet)]
////mod notyet {
////    use super::ek;
////    use super::helpers::*;
////    fn metacommand<'a, 'b>(
////        input: ek::LocatedSpan<'a, 'b>,
////    ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////        fn double_hand<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, Option<char>> {
////            fn hand<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
////                char('☛')(input)
////            }
////
////            preceded(
////                hand,
////                ek::expect(hand, "'☛' should be followed by another '☛'"),
////            )(input)
////        }
////
////        fn punch<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////            match map_res(
////                // We interpret "AA" in the descripion of the PUNCH
////                // metacommand as accepting only literal numeric (and not
////                // symbolic) values.  That may not be a correct
////                // interpretation, though.
////                preceded(preceded(tag("PUNCH"), spaces1), opt(literal)),
////                helpers::punch_address,
////            )(input)
////            {
////                Ok((input, punch)) => {
////                    let cmd: ManuscriptMetaCommand = ManuscriptMetaCommand::Punch(punch);
////                    Ok((input, cmd))
////                }
////                Err(nom::Err::Error(e) | nom::Err::Failure(e)) => {
////                    let err = Error(
////                        ErrorLocation::from(&e.input),
////                        "invalid PUNCH address".to_string(),
////                    );
////                    e.input.extra.report_error(err);
////                    Ok((e.input, ManuscriptMetaCommand::Invalid))
////                }
////                Err(e) => Err(e),
////            }
////        }
////
////        fn base_change<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////            fn decimal<'a, 'b>(
////                input: ek::LocatedSpan<'a, 'b>,
////            ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////                map(alt((tag("DECIMAL"), tag("DEC"))), |_| {
////                    ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)
////                })(input)
////            }
////            fn octal<'a, 'b>(
////                input: ek::LocatedSpan<'a, 'b>,
////            ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////                map(alt((tag("OCTAL"), tag("OCT"))), |_| {
////                    ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)
////                })(input)
////            }
////
////            alt((decimal, octal))(input)
////        }
////
////        fn metacommand_body<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, ManuscriptMetaCommand> {
////            alt((base_change, punch))(input)
////        }
////
////        map(
////            pair(
////                double_hand,
////                ek::expect(
////                    metacommand_body,
////                    "double meta hand '☛☛' must be followed by a valid meta command",
////                ),
////            ),
////            |got| match got {
////                (Some(_), Some(cmd)) => cmd,
////                _ => ManuscriptMetaCommand::Invalid,
////            },
////        )(input)
////    }
////
////    fn maybe_hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
////        /// Accept either 'h' or ':' signalling the hold bit should be set.
////        /// The documentation seems to use both, though perhaps ':' is the
////        /// older usage.
////        fn hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
////            map(alt((tag("h"), tag(":"))), |_| HoldBit::Hold)(input)
////        }
////
////        fn not_hold<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, HoldBit> {
////            map(
////                alt((
////                    // Accept a combining overbar with h, as used on the TX-2.
////                    tag("\u{0305}h"),
////                    // Also accept the "h with stroke" (better known as h-bar) symbol.
////                    tag("ℏ"),
////                )),
////                |_| HoldBit::NotHold,
////            )(input)
////        }
////
////        let holdmapper = |got: Option<HoldBit>| got.unwrap_or(HoldBit::Unspecified);
////        map(opt(preceded(space0, alt((hold, not_hold)))), holdmapper)(input)
////    }
////
////    fn program_instruction<'a, 'b>(
////        input: ek::LocatedSpan<'a, 'b>,
////    ) -> ek::IResult<'a, 'b, ProgramInstruction> {
////        fn build_inst(
////            parts: (Option<SymbolName>, HoldBit, Vec<InstructionFragment>),
////        ) -> ProgramInstruction {
////            let (maybe_tag, holdbit, fragments) = parts;
////            ProgramInstruction {
////                tag: maybe_tag,
////                holdbit,
////                parts: fragments,
////            }
////        }
////
////        fn program_instruction_fragments<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, Vec<InstructionFragment>> {
////            many1(program_instruction_fragment)(input)
////        }
////
////        map(
////            tuple((
////                opt(tag_definition),
////                maybe_hold,
////                program_instruction_fragments,
////            )),
////            build_inst,
////        )(input)
////    }
////
////    fn execute_metacommand(state_extra: &StateExtra, cmd: &ManuscriptMetaCommand) {
////        match cmd {
////            ManuscriptMetaCommand::Invalid => {
////                // Error messages about invalid metacommands are
////                // accumulated in the parser state and don't need to be
////                // separately reported.
////            }
////            ManuscriptMetaCommand::Punch(_) => {
////                // Instead of executing this metacommand as we parse it,
////                // we simply return it as part of the parser output, and
////                // it is executed by the driver.
////            }
////            ManuscriptMetaCommand::BaseChange(new_base) => state_extra.set_numeral_mode(*new_base),
////        }
////    }
////
////    fn statement<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Statement> {
////        /// Assginments are called "equalities" in the TX-2 Users Handbook.
////        /// See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
////        /// AUTOMATIC ASSIGNMENT".
////        fn assignment<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, (SymbolName, Expression)> {
////            let equals = delimited(space0, tag("="), space0);
////            separated_pair(parse_symex, equals, expression)(input)
////        }
////
////        alt((
////            // We have to parse an assignment first here, in order to
////            // accept "FOO=2" as an assignment rather than the instruction
////            // fragment "FOO" followed by a syntax error.
////            map(assignment, |(sym, val)| Statement::Assignment(sym, val)),
////            map(program_instruction, Statement::Instruction),
////        ))(input)
////    }
////
////    fn manuscript_line<'a, 'b>(
////        input: ek::LocatedSpan<'a, 'b>,
////    ) -> ek::IResult<'a, 'b, ManuscriptLine> {
////        fn parse_and_execute_metacommand<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, ManuscriptLine> {
////            match metacommand(input) {
////                Ok((tail, cmd)) => {
////                    execute_metacommand(&tail.extra, &cmd);
////                    Ok((tail, ManuscriptLine::MetaCommand(cmd)))
////                }
////                Err(e) => Err(e),
////            }
////        }
////
////        fn build_code_line(parts: (Option<Address>, Statement)) -> ManuscriptLine {
////            let maybe_origin: Option<Origin> = parts.0.map(Origin);
////            ManuscriptLine::Code(maybe_origin, parts.1)
////        }
////
////        fn origin<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, Address> {
////            terminated(address_expression, pair(space0, tag("|")))(input)
////        }
////        let origin_only = map(origin, |address| {
////            ManuscriptLine::JustOrigin(Origin(address))
////        });
////
////        let line = alt((
////            parse_and_execute_metacommand,
////            map(pair(opt(origin), statement), build_code_line),
////            // Because we prefer to parse a statement if one exists,
////            // the origin_only alternative has to appear after the
////            // alternative which parses a statement.
////            origin_only,
////        ));
////
////        preceded(space0, line)(input)
////    }
////
////    fn comment<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, String> {
////        map(
////            recognize(preceded(preceded(space0, tag("**")), take_until("\n"))),
////            |text: ek::LocatedSpan| text.fragment().to_string(),
////        )(input)
////    }
////
////    fn newline<'a, 'b>(input: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, char> {
////        char('\n')(input)
////    }
////
////    fn end_of_line<'a, 'b>(
////        input: ek::LocatedSpan<'a, 'b>,
////    ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
////        fn one_end_of_line<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, ek::LocatedSpan<'a, 'b>> {
////            recognize(preceded(preceded(space0, opt(comment)), newline))(input)
////        }
////
////        recognize(many1(one_end_of_line))(input)
////    }
////
////    fn source_file<'a, 'b>(body: ek::LocatedSpan<'a, 'b>) -> ek::IResult<'a, 'b, SourceFile> {
////        // Parse a manuscript (which is a sequence of metacommands, macros
////        // and assembly-language instructions).
////        fn parse_nonempty_source_file<'a, 'b>(
////            input: ek::LocatedSpan<'a, 'b>,
////        ) -> ek::IResult<'a, 'b, SourceFile> {
////            // TODO: when we implement metacommands we will need to separate
////            // the processing of the metacommands and the generation of the
////            // assembled code, because in between those things has to come the
////            // execution of metacommands such as INSERT, DELETE, REPLACE.
////            let parse_source_lines = preceded(
////                many0(end_of_line),
////                many0(terminated(
////                    manuscript_line,
////                    ek::expect(end_of_line, "expected newline after a program instruction"),
////                )),
////            );
////
////            map(parse_source_lines, |lines| {
////                let (blocks, punch) = helpers::manuscript_lines_to_blocks(lines);
////                SourceFile { blocks, punch }
////            })(input)
////        }
////
////        terminated(parse_nonempty_source_file, ek::expect_end_of_file)(body)
////    }
////
////    pub(crate) fn parse_source_file(
////        source_file_body: &str,
////        setup: fn(&mut State),
////    ) -> (SourceFile, Vec<Error>) {
////        ek::parse_with(source_file_body, source_file, setup)
////    }
////
////    impl<'a, 'b> SymbolName {
////        // Symexes "TYPE A" and "TYPEA" are equivalent.
////        fn canonical(span: &ek::LocatedSpan<'a, 'b>) -> String {
////            (*span.fragment())
////                .chars()
////                .filter(|ch: &char| -> bool { *ch != ' ' })
////                .collect()
////        }
////    }
////
////    impl<'a, 'b> From<&ek::LocatedSpan<'a, 'b>> for SymbolName {
////        fn from(location: &ek::LocatedSpan<'a, 'b>) -> SymbolName {
////            SymbolName {
////                canonical: SymbolName::canonical(location),
////                //as_used: location.fragment().to_string(),
////            }
////        }
////    }
////}

// Local Variables:
// mode: rustic
// lsp-rust-analyzer-server-display-inlay-hints: nil
// End:
