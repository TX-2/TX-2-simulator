mod helpers;
mod symex;
mod terminal;
#[cfg(test)]
mod tests;

use chumsky::error::Rich;
use chumsky::extra::Full;
use chumsky::input::{StrInput, ValueInput};
use chumsky::prelude::{choice, recursive, Input, IterParser};
use chumsky::Parser;

use super::ast::*;
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::types::*;
use base::charset::Script;
use base::prelude::*;
use helpers::Sign;

pub(crate) type Extra<'a, T> = Full<Rich<'a, T>, NumeralMode, ()>;

fn literal<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, LiteralValue, Extra<'a, char>> + Clone
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + Clone,
{
    let opt_sign = choice((
        terminal::plus(script_required).to(Sign::Plus),
        terminal::minus(script_required).to(Sign::Minus),
    ))
    .or_not()
    .labelled("sign");
    let maybe_dot = terminal::dot(script_required).or_not().map(|x| x.is_some());

    opt_sign
        .then(terminal::digit1(script_required))
        .then(maybe_dot)
        .try_map_with_state(move |((maybe_sign, digits), hasdot), span, state| {
            match helpers::make_num(maybe_sign, &digits, hasdot, state) {
                Ok(value) => Ok(LiteralValue::from((span, script_required, value))),
                Err(e) => Err(Rich::custom(span, e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn here<'a, I>(script_required: Script) -> impl Parser<'a, I, Atom, Extra<'a, char>> + Clone
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    terminal::hash(script_required).to(Atom::Here(script_required))
}

fn build_arithmetic_expression(
    (head, tail): (Atom, Vec<(Operator, Atom)>),
) -> ArithmeticExpression {
    ArithmeticExpression::with_tail(head, tail)
}

/// Parse a sequence of values (symbolic or literal) and arithmetic
/// operators.
///
/// BAT² is not an identifier but a sequence[1] whose value is
/// computed by OR-ing the value of the symex BAT with the value of
/// the literal "²" (which is 2<<30, or 0o20_000_000_000).  But BAT²
/// is itself not a molecule (because there is a script change).
/// However probably (BAT²) should be parsed as an atom.
///
/// [1] I use "sequence" in the paragraph above to avoid saying
/// "expression" or "instruction fragment".
fn arithmetic_expression<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, ArithmeticExpression, Extra<'a, char>> + Clone
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    // We use recursive here to prevent the parser blowing the stack
    // when trying to parse inputs which have parentheses - that is,
    // inputs that require recursion.
    recursive(|arithmetic_expression| {
        let parenthesised_arithmetic_expression = arithmetic_expression // this is the recursive call
            .clone()
            .delimited_by(
                terminal::left_paren(script_required),
                terminal::right_paren(script_required),
            )
            .map(|expr| Atom::Parens(Box::new(expr)));

        let non_opcode_atom = choice((
            literal(script_required).map(Atom::from),
            here(script_required).map(Atom::from),
            symbol(script_required)
                .map_with_span(move |name, span| Atom::Symbol(span, script_required, name)),
            parenthesised_arithmetic_expression,
        ));

        let atom_in_script = terminal::opcode()
            .map(Atom::from)
            .or(non_opcode_atom)
            .boxed();

        let operator_with_atom_in_script = terminal::operator(script_required)
            .padded_by(terminal::horizontal_whitespace0())
            .then(
                atom_in_script
                    .clone()
                    .padded_by(terminal::horizontal_whitespace0()),
            );

        atom_in_script
            .then(operator_with_atom_in_script.repeated().collect())
            .map(build_arithmetic_expression)
    })
}

fn symbol<'a, I>(script_required: Script) -> impl Parser<'a, I, SymbolName, Extra<'a, char>> + Clone
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    symex::parse_symex(script_required)
        .map(SymbolName::from)
        .labelled("symex (symbol) name")
}

fn tag_definition<'a, I>() -> impl Parser<'a, I, Tag, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    let arrow = terminal::arrow().padded_by(terminal::horizontal_whitespace0());
    symbol(Script::Normal)
        .map_with_span(|name, span| Tag { name, span })
        .then_ignore(arrow)
        .then_ignore(terminal::horizontal_whitespace0())
        .labelled("tag definition")
}

fn program_instruction_fragment<'srcbody, I>(
) -> impl Parser<'srcbody, I, InstructionFragment, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = Span> + StrInput<'srcbody, char> + Clone,
{
    fn frag<'a, I>(
        script_required: Script,
    ) -> impl Parser<'a, I, InstructionFragment, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        arithmetic_expression(script_required)
            .padded_by(terminal::horizontal_whitespace0())
            .map(InstructionFragment::from)
    }

    choice((frag(Script::Normal), frag(Script::Super), frag(Script::Sub)))
}

fn program_instruction_fragments<'srcbody, I>(
) -> impl Parser<'srcbody, I, Vec<InstructionFragment>, Extra<'srcbody, char>>
where
    I: Input<'srcbody, Token = char, Span = Span> + StrInput<'srcbody, char> + Clone,
{
    program_instruction_fragment()
        .repeated()
        .at_least(1)
        .collect()
        .labelled("program instruction")
}

fn metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    fn named_metacommand<'a, I>(name: &'static str) -> impl Parser<'a, I, (), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        terminal::metacommand_name()
            .filter(move |n| *n == name)
            .ignored()
    }

    fn punch<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        // We currently have a limitation in the interpretation of
        // "AA" in the PUNCH metacommand.  The documentation clearly
        // states that this should be an honest tag.  We currently
        // accept only numeric literals.
        named_metacommand("PUNCH")
            .then(terminal::horizontal_whitespace1())
            .ignore_then(literal(Script::Normal).or_not())
            .try_map(|aa, span| match helpers::punch_address(aa) {
                Ok(punch) => Ok(ManuscriptMetaCommand::Punch(punch)),
                Err(msg) => Err(Rich::custom(span, msg)),
            })
            .labelled("PUNCH command")
    }

    fn base_change<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
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

fn untagged_program_instruction<'a, I>(
) -> impl Parser<'a, I, UntaggedProgramInstruction, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    let maybe_hold = terminal::hold()
        .or_not()
        .padded_by(terminal::horizontal_whitespace0())
        .labelled("instruction hold bit");
    maybe_hold
        .then(program_instruction_fragments())
        .map_with_span(
            |(maybe_hold, parts): (Option<HoldBit>, Vec<InstructionFragment>), span| {
                UntaggedProgramInstruction {
                    span,
                    holdbit: maybe_hold.unwrap_or(HoldBit::Unspecified),
                    parts,
                }
            },
        )
}

fn tagged_program_instruction<'a, I>(
) -> impl Parser<'a, I, TaggedProgramInstruction, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    tag_definition()
        .or_not()
        .then(untagged_program_instruction())
        .map(
            |(tag, instruction): (Option<Tag>, UntaggedProgramInstruction)| {
                TaggedProgramInstruction { tag, instruction }
            },
        )
        .labelled("optional tag definition followed by a program instruction")
}

fn statement<'a, I>() -> impl Parser<'a, I, Statement, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    /// Assginments are called "equalities" in the TX-2 Users Handbook.
    /// See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
    /// AUTOMATIC ASSIGNMENT".
    fn assignment<'a, I>(
    ) -> impl Parser<'a, I, (SymbolName, UntaggedProgramInstruction), Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        terminal::horizontal_whitespace0()
            .ignore_then(symex::parse_symex(Script::Normal))
            .then_ignore(terminal::equals().padded_by(terminal::horizontal_whitespace0()))
            .then(untagged_program_instruction())
    }

    choice((
        // We have to parse an assignment first here, in order to
        // accept "FOO=2" as an assignment rather than the instruction
        // fragment "FOO" followed by a syntax error.
        assignment().map_with_span(|(sym, inst), span| Statement::Assignment(span, sym, inst)),
        tagged_program_instruction().map(Statement::Instruction),
    ))
}

fn manuscript_line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
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

    fn parse_and_execute_metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        metacommand()
            .map_with_state(|cmd, _span, state| {
                execute_metacommand(state, &cmd);
                ManuscriptLine::MetaCommand(cmd)
            })
            .labelled("metacommand")
    }

    fn build_code_line(parts: (Option<Origin>, Statement)) -> ManuscriptLine {
        ManuscriptLine::Code(parts.0, parts.1)
    }

    fn line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
    {
        fn origin<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a, char>>
        where
            I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
        {
            /// An address expression is a literal value or a symex.  That is I
            /// think it's not required that an arithmetic expression
            /// (e.g. "5+BAR") be accepted in an origin notation (such as
            /// "<something>|").
            fn literal_address_expression<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a, char>>
            where
                I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + Clone,
            {
                // We should eventually support symexes here.
                literal(Script::Normal)
                    .try_map(|lit, span| match Address::try_from(lit.value()) {
                        Ok(addr) => Ok(Origin::Literal(span, addr)),
                        Err(e) => Err(Rich::custom(span, format!("not a valid address: {e}"))),
                    })
                    .labelled("literal address expression")
            }

            fn symbolic_address_expression<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a, char>>
            where
                I: Input<'a, Token = char, Span = Span>
                    + ValueInput<'a>
                    + StrInput<'a, char>
                    + Clone,
            {
                symbol(Script::Normal)
                    .map_with_span(|sym, span| Origin::Symbolic(span, sym))
                    .labelled("symbolic address expression")
            }
            choice((literal_address_expression(), symbolic_address_expression()))
                .padded_by(terminal::horizontal_whitespace0())
                .then_ignore(terminal::pipe())
        }

        let optional_origin_with_statement = origin()
            .or_not()
            .then(statement())
            .map(build_code_line)
            .labelled("statement with origin");

        let origin_only = origin().map(ManuscriptLine::JustOrigin).labelled("origin");

        choice((
            // Ignore whitespace after the metacommand but not before it.
            parse_and_execute_metacommand(),
            optional_origin_with_statement,
            // Because we prefer to parse a statement if one exists,
            // the origin_only alternative has to appear after the
            // alternative which parses a statement.
            origin_only,
        ))
    }

    line()
}

fn end_of_line<'a, I>() -> impl Parser<'a, I, (), Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + StrInput<'a, char> + Clone,
{
    let one_end_of_line = terminal::horizontal_whitespace0()
        .then(terminal::comment().or_not())
        .then(chumsky::text::newline())
        .ignored();

    one_end_of_line
        .repeated()
        .at_least(1)
        .ignored()
        .labelled("comment or end-of-line")
}

fn terminated_manuscript_line<'a, I>() -> impl Parser<'a, I, Option<ManuscriptLine>, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    // If we support INSERT, DELETE, REPLACE, we will need to
    // separate the processing of the metacommands and the
    // generation of the assembled code.
    manuscript_line().or_not().then_ignore(end_of_line())
}

pub(crate) fn source_file<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a, char>>
where
    I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
{
    // Parse a manuscript (which is a sequence of metacommands, macros
    // and assembly-language instructions).
    fn source_file_as_blocks<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a, char>>
    where
        I: Input<'a, Token = char, Span = Span> + ValueInput<'a> + StrInput<'a, char> + Clone,
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
