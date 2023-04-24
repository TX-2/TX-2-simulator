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
    one_of("\u{22C5}\u{00B7}")
        .or_not()
        .map(|x| x.is_some())
        .labelled("dot")
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
        .labelled("superscript octal digits")
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
    .labelled("superscript dot")
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
    expression().padded().map(InstructionFragment::from)
}

fn spaces1<'srcbody, I>() -> impl Parser<'srcbody, I, (), Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    just(' ')
        .repeated()
        .at_least(1)
        .ignored()
        .labelled("one or more spaces")
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

    fn parse_nonblank_simple_symex_chars<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        any()
            .filter(|ch| is_nonblank_simple_symex_char(*ch))
            .repeated()
            .at_least(1)
            .collect()
            .labelled("nonblank simple symex character")
    }

    fn concat_strings(mut s: String, next: String) -> String {
        s.push_str(&next);
        s
    }

    // Compound chars are not supported at the moment, see docs/assembler/index.md.
    fn parse_symex_syllable<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        parse_nonblank_simple_symex_chars()
            .foldl(
                parse_nonblank_simple_symex_chars().repeated(),
                concat_strings,
            )
            .labelled("symex syllable")
    }

    pub(super) fn parse_symex_reserved_syllable<'a, I>(
    ) -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        parse_symex_syllable()
            .try_map(|syllable, span| {
                if is_reserved_identifier(&syllable) {
                    Ok(syllable)
                } else {
                    Err(Rich::custom(span, "expected reserved syllable".to_string()))
                }
            })
            .labelled("reserved symex")
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
            .foldl(parse_symex_syllable().padded().repeated(), concat_strings)
            .labelled("multi-syllable symex")
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
        .labelled("symbol name")
    }
}

fn literal<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((normal_literal(), superscript_literal(), subscript_literal()))
        .labelled("numeric literal")
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

/// Parse an expression; these can currently only take the form of a literal.
/// TX-2's M4 assembler allows arithmetic expressions also, but these are not
/// currently implemented.
///
/// When we do implement fuller support for expressions, we need to pay
/// attention to the rules for symex termination (see section 6-2.3
/// "RULES FOR SYMEX FORMATION" item 8), because script changes
/// terminate symexes.
///
/// This means that BAT² is not an identifier but a sequence[1] whose
/// value is computed by OR-ing the value of the symex BAT with the
/// value of the literal "²" (which is 2<<30, or 0o20_000_000_000).
/// Whether BAT² is itself an expression or an "InstructionFragment" is
/// something we will need to consider carefully.  For example, is
/// (BAT²) valid?  If yes, then so is (BAT²)+1, meaning that our
/// current rule for instruction_fragment may have to change
/// significantly.
///
/// [1] I use "sequence" in the paragraph above to avoid saying
/// "expression" or "instruction fragment".
fn expression<'a, I>() -> impl Parser<'a, I, Expression, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    fn literal_expression<'a, I>() -> impl Parser<'a, I, Expression, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((literal(), opcode())).map(Expression::from)
    }

    fn symbolic_expression<'a, I>() -> impl Parser<'a, I, Expression, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        symbol().map(|name| Expression::Symbol(Elevation::Normal, name))
    }

    choice((literal_expression(), symbolic_expression()))
}

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

fn symbol<'a, I>() -> impl Parser<'a, I, SymbolName, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    symex::parse_symex()
        .map(SymbolName::from)
        .labelled("symex (symbol) name")
}

fn tag_definition<'a, I>() -> impl Parser<'a, I, SymbolName, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let just_arrow = choice((just("->"), just("\u{2192}")));
    symbol()
        .then_ignore(just_arrow.padded())
        .labelled("tag definition")
}

fn double_hand<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    let hand = just('☛');
    hand.ignored()
        .then(hand)
        .ignored()
        .labelled("double meta hand")
}

fn metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    fn punch<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        // We currently have a limitation in the interpretation of
        // "AA" in the PUNCH metacommand.  The documentation clearly
        // states that this should be an honest tag.  We currently
        // accept only numeric literals.
        just("PUNCH")
            .then(inline_whitespace())
            .ignore_then(literal().or_not())
            .try_map(|aa, span| match helpers::punch_address(aa) {
                Ok(punch) => Ok(ManuscriptMetaCommand::Punch(punch)),
                Err(msg) => Err(Rich::custom(span, msg)),
            })
            .labelled("PUNCH command")
    }

    fn base_change<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        choice((
            choice((just("DECIMAL"), just("DEC")))
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)),
            choice((just("OCTAL"), just("OCT")))
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)),
        ))
        .labelled("base-change metacommand")
    }

    fn metacommand_body<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        choice((base_change(), punch()))
    }

    double_hand()
        .ignore_then(metacommand_body())
        .labelled("metacommand")
}

fn hold<'a, I>() -> impl Parser<'a, I, HoldBit, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // Accept either 'h' or ':' signalling the hold bit should be set.
    // The documentation seems to use both, though perhaps ':' is the
    // older usage.
    let h = one_of("h:").to(HoldBit::Hold);
    let nh = just("\u{0305}h").or(just("ℏ")).to(HoldBit::NotHold);
    choice((h, nh)).padded().labelled("instruction hold bit")
}

fn program_instruction_fragments<'a, I>(
) -> impl Parser<'a, I, Vec<InstructionFragment>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    program_instruction_fragment()
        .repeated()
        .at_least(1)
        .collect()
        .labelled("program instruction")
}

fn hold_and_fragments<'a, I>(
) -> impl Parser<'a, I, (HoldBit, Vec<InstructionFragment>), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    //maybe_hold().then(program_instruction_fragments())
    program_instruction_fragments().map(|frags| (HoldBit::Unspecified, frags))
}

fn program_instruction<'a, I>() -> impl Parser<'a, I, ProgramInstruction, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    fn build_inst(parts: (Option<SymbolName>, Vec<InstructionFragment>)) -> ProgramInstruction {
        let (maybe_tag, fragments) = parts;
        let holdbit = None;
        ProgramInstruction {
            tag: maybe_tag,
            holdbit: holdbit.unwrap_or(HoldBit::Unspecified),
            parts: fragments,
        }
    }

    tag_definition()
        .or_not()
        .then(program_instruction_fragments())
        .map(build_inst)
        .padded()
        .labelled("optional tag definition followed by a program instruction")
}

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
