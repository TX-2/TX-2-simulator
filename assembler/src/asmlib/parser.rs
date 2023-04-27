// This code is not yet used, but I don't want to comment things out
// or ass cfg conditionals as I will simply need to reverse them when
// we do start using it.

mod helpers;
mod terminal;
#[cfg(test)]
mod tests;

use chumsky::error::Rich;
use chumsky::extra::Full;
use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::{choice, Input, IterParser, SimpleSpan};
use chumsky::Parser;

use super::ast::*;
use super::state::NumeralMode;
use base::prelude::*;
use helpers::Sign;

pub(crate) type Extra<'a, T> = Full<Rich<'a, T>, NumeralMode, ()>;

fn opt_sign<'a, I>() -> impl Parser<'a, I, Option<Sign>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    choice((
        terminal::plus().to(Sign::Plus),
        terminal::minus().to(Sign::Minus),
    ))
    .or_not()
    .labelled("sign")
}

fn maybe_dot<'a, I>() -> impl Parser<'a, I, bool, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    terminal::dot().or_not().map(|x| x.is_some())
}

fn normal_literal<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    opt_sign()
        .then(terminal::digits1())
        .then(maybe_dot())
        .try_map_with_state(|((maybe_sign, digits), hasdot), span, state| {
            match helpers::make_num(maybe_sign, &digits, hasdot, state) {
                Ok(value) => Ok(LiteralValue::from((Elevation::Normal, value))),
                Err(e) => Err(Rich::custom(span, e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn maybe_superscript_dot<'srcbody, I>() -> impl Parser<'srcbody, I, bool, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    terminal::superscript_dot()
        .or_not()
        .map(|x| x.is_some())
        .labelled("superscript dot")
}

fn superscript_literal<'srcbody, I>(
) -> impl Parser<'srcbody, I, LiteralValue, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
{
    fn superscript_sign<'srcbody, I>() -> impl Parser<'srcbody, I, Sign, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            terminal::superscript_plus().to(Sign::Plus),
            terminal::superscript_minus().to(Sign::Minus),
        ))
    }

    superscript_sign()
        .or_not()
        .then(terminal::superscript_digit1())
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
    fn subscript_sign<'srcbody, I>() -> impl Parser<'srcbody, I, Sign, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        choice((
            terminal::subscript_minus().to(Sign::Minus),
            terminal::subscript_plus().to(Sign::Plus),
        ))
    }

    fn subscript_oct_digit1<'srcbody, I>() -> impl Parser<'srcbody, I, String, Extra<'srcbody, char>>
    where
        I: Input<'srcbody, Token = char, Span = SimpleSpan> + ValueInput<'srcbody>,
    {
        terminal::subscript_oct_digit()
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
        terminal::subscript_dot().or_not().map(|x| x.is_some())
    }

    (subscript_sign().or_not())
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
    expression()
        .padded_by(opt_horizontal_whitespace())
        .map(InstructionFragment::from)
}

mod symex {
    use chumsky::input::ValueInput;
    use chumsky::prelude::*;
    use chumsky::Parser;

    use super::helpers::{self, DecodedOpcode};
    use super::terminal;
    use super::{opt_horizontal_whitespace, Extra, SymbolName};

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
    fn parse_symex_syllable<'a, I>() -> impl Parser<'a, I, String, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        terminal::nonblank_simple_symex_chars()
            .foldl(
                terminal::nonblank_simple_symex_chars().repeated(),
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
        parse_symex_non_reserved_syllable()
            .foldl(
                parse_symex_syllable()
                    .padded_by(opt_horizontal_whitespace())
                    .repeated(),
                concat_strings,
            )
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
        choice((literal(), terminal::opcode())).map(Expression::from)
    }

    fn symbolic_expression<'a, I>() -> impl Parser<'a, I, Expression, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
    {
        symbol().map(|name| Expression::Symbol(Elevation::Normal, name))
    }

    choice((literal_expression(), symbolic_expression()))
}

/// An address expression is a literal value or a symex.  That is I
/// think it's not required that an arithmetic expression
/// (e.g. "5+BAR") be accepted in an origin notation (such as
/// "<something>|").
fn address_expression<'a, I>() -> impl Parser<'a, I, Address, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    // We should eventually support symexes here.
    literal()
        .try_map(|lit, span| match Address::try_from(lit.value()) {
            Ok(addr) => Ok(addr),
            Err(e) => Err(Rich::custom(span, format!("not a valid address: {e}"))),
        })
        .labelled("address expression")
}

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
    let arrow = terminal::arrow().padded_by(opt_horizontal_whitespace());
    symbol().then_ignore(arrow).labelled("tag definition")
}

fn named_metacommand<'a, I>(name: &'static str) -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    terminal::metacommand_name()
        .filter(move |n| n == name)
        .then(terminal::inline_whitespace())
        .ignored()
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
        named_metacommand("PUNCH")
            .ignore_then(literal().or_not())
            .try_map(|aa, span| match helpers::punch_address(aa) {
                Ok(punch) => Ok(ManuscriptMetaCommand::Punch(punch)),
                Err(msg) => Err(Rich::custom(span, msg)),
            })
            .labelled("PUNCH command")
    }

    fn base_change<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        choice((
            choice((named_metacommand("DECIMAL"), named_metacommand("DEC")))
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)),
            choice((named_metacommand("OCTAL"), named_metacommand("OCT")))
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)),
        ))
        .labelled("base-change metacommand")
    }

    choice((base_change(), punch())).labelled("metacommand")
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

fn program_instruction<'a, I>() -> impl Parser<'a, I, ProgramInstruction, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    fn build_inst(
        parts: (
            Option<SymbolName>,
            (Option<HoldBit>, Vec<InstructionFragment>),
        ),
    ) -> ProgramInstruction {
        let (maybe_tag, (holdbit, fragments)) = parts;
        ProgramInstruction {
            tag: maybe_tag,
            holdbit: holdbit.unwrap_or(HoldBit::Unspecified),
            parts: fragments,
        }
    }

    fn maybe_hold<'a, I>() -> impl Parser<'a, I, Option<HoldBit>, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        terminal::hold()
            .or_not()
            .padded_by(opt_horizontal_whitespace())
            .labelled("instruction hold bit")
    }

    fn hold_and_fragments<'a, I>(
    ) -> impl Parser<'a, I, (Option<HoldBit>, Vec<InstructionFragment>), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        maybe_hold().then(program_instruction_fragments())
    }

    tag_definition()
        .or_not()
        .then(hold_and_fragments())
        .map(build_inst)
        .labelled("optional tag definition followed by a program instruction")
}

fn execute_metacommand(state: &mut NumeralMode, cmd: &ManuscriptMetaCommand) {
    match cmd {
        ManuscriptMetaCommand::Punch(_) => {
            // Instead of executing this metacommand as we parse it,
            // we simply return it as part of the parser output, and
            // it is executed by the driver.
        }
        ManuscriptMetaCommand::BaseChange(new_base) => state.set_numeral_mode(*new_base),
    }
}

fn statement<'a, I>() -> impl Parser<'a, I, Statement, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    /// Assginments are called "equalities" in the TX-2 Users Handbook.
    /// See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
    /// AUTOMATIC ASSIGNMENT".
    fn assignment<'a, I>() -> impl Parser<'a, I, (SymbolName, Expression), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        symex::parse_symex()
            .then_ignore(terminal::equals().padded_by(opt_horizontal_whitespace()))
            .then(expression())
            .padded_by(opt_horizontal_whitespace())
    }

    choice((
        // We have to parse an assignment first here, in order to
        // accept "FOO=2" as an assignment rather than the instruction
        // fragment "FOO" followed by a syntax error.
        assignment().map(|(sym, val)| Statement::Assignment(sym, val)),
        program_instruction().map(Statement::Instruction),
    ))
}

/// Matches and ignores zero or more horizontal-whitespace characters.
/// That is, spaces or tabs but not newlines or carriage returns.  We
/// also don't match backspaces, because eventually those need to be
/// supported as part of a compound character.
fn opt_horizontal_whitespace<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a>,
{
    terminal::horizontal_whitespace().repeated().ignored()
}

fn manuscript_line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    fn parse_and_execute_metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        metacommand()
            .map_with_state(|cmd, _span, state| {
                execute_metacommand(state, &cmd);
                ManuscriptLine::MetaCommand(cmd)
            })
            .labelled("metacommand")
    }

    fn build_code_line(parts: (Option<Address>, Statement)) -> ManuscriptLine {
        let maybe_origin: Option<Origin> = parts.0.map(Origin);
        ManuscriptLine::Code(maybe_origin, parts.1)
    }

    fn origin<'a, I>() -> impl Parser<'a, I, Address, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        address_expression()
            .padded_by(opt_horizontal_whitespace())
            .then_ignore(terminal::pipe())
    }

    fn origin_only<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        origin()
            .map(|address| ManuscriptLine::JustOrigin(Origin(address)))
            .labelled("origin")
    }

    fn optional_origin_with_statement<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        origin()
            .or_not()
            .then(statement())
            .map(build_code_line)
            .labelled("statement with origin")
    }

    fn line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        choice((
            // Ignore whitespace after the metacommand but not before it.
            parse_and_execute_metacommand(),
            optional_origin_with_statement(),
            // Because we prefer to parse a statement if one exists,
            // the origin_only alternative has to appear after the
            // alternative which parses a statement.
            origin_only(),
        ))
    }

    line()
}

fn end_of_line<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + StrInput<'a, char>,
{
    fn one_end_of_line<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + StrInput<'a, char>,
    {
        terminal::inline_whitespace()
            .or_not()
            .then(terminal::comment().or_not())
            .then(chumsky::text::newline())
            .ignored()
    }

    one_end_of_line()
        .repeated()
        .at_least(1)
        .ignored()
        .labelled("comment or end-of-line")
}

fn terminated_manuscript_line<'a, I>() -> impl Parser<'a, I, Option<ManuscriptLine>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    // If we support INSERT, DELETE, REPLACE, we will need to
    // separate the processing of the metacommands and the
    // generation of the assembled code.
    manuscript_line()
        .map_with_span(|ml, span| {
            eprintln!("recognised manuscript_line {ml:?} at {span:?}");
            ml
        })
        .or_not()
        .then_ignore(end_of_line().map_with_span(|_, span| {
            eprintln!("recognised end_of_line at {span:?}");
        }))
}

fn source_file<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
{
    // Parse a manuscript (which is a sequence of metacommands, macros
    // and assembly-language instructions).
    fn source_file_as_blocks<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = SimpleSpan> + ValueInput<'a> + StrInput<'a, char>,
    {
        terminated_manuscript_line().repeated().collect().map(
            |lines: Vec<Option<ManuscriptLine>>| {
                // Filter out empty lines.
                let lines: Vec<ManuscriptLine> = lines.into_iter().flatten().collect();
                let (blocks, punch) = helpers::manuscript_lines_to_blocks(lines);
                SourceFile { blocks, punch }
            },
        )
    }
    source_file_as_blocks().then_ignore(terminal::end_of_input())
}

pub(crate) fn parse_source_file(
    source_file_body: &str,
    setup: fn(&mut NumeralMode),
) -> (Option<SourceFile>, Vec<Rich<'_, char>>) {
    let mut state = NumeralMode::default();
    setup(&mut state);
    source_file()
        .parse_with_state(source_file_body, &mut state)
        .into_output_errors()
}

// Local Variables:
// mode: rustic
// lsp-rust-analyzer-server-display-inlay-hints: nil
// End:
