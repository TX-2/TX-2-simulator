use std::{
    fmt::Debug,
    ops::{Deref, Range, Shl},
};

pub(crate) mod helpers;
mod symex;
#[cfg(test)]
mod tests;

use chumsky::error::Rich;
use chumsky::extra::Full;
use chumsky::input::{Stream, ValueInput};
use chumsky::inspector::SimpleState;
use chumsky::prelude::{choice, just, one_of, recursive, Input, IterParser, SimpleSpan};
use chumsky::select;
use chumsky::Parser;

use super::ast::*;
use super::glyph::Unrecognised;
use super::lexer::{self};
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::types::*;
use base::charset::Script;
use base::prelude::*;
use helpers::Sign;

pub(crate) type Extra<'a> = Full<Rich<'a, lexer::Token>, SimpleState<NumeralMode>, ()>;
use lexer::Token as Tok;

fn literal<'a, I>(script_required: Script) -> impl Parser<'a, I, LiteralValue, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let maybe_sign = choice((
        just(Tok::Plus(script_required)).to(Sign::Plus),
        just(Tok::Minus(script_required)).to(Sign::Minus),
    ))
    .map_with(|maybe_sign, extra| (maybe_sign, extra.span()))
    .or_not();

    let digits = select! {
        Tok::Digits(script, n) if script == script_required => n,
    }
    .map_with(|digits, extra| (digits, extra.span()));

    // We want to accept "-1" as a signed number, but not "- 1".  So
    // we reject tokens which have a gap between them.  This also
    // means there cannot be an annotation between them, despite the
    // fact that annotations are supposed to be otherwise invisible.
    fn immediately_adjoining<T: Debug, U: Debug>(found: &(Option<(T, Span)>, (U, Span))) -> bool {
        match found.0.as_ref() {
            Some((_, sign_span)) => sign_span.end == found.1 .1.start,
            _ => true,
        }
    }

    fn discard_spans<T, U>(spanned: (Option<(T, Span)>, (U, Span))) -> (Option<T>, U) {
        (spanned.0.map(|x| x.0), spanned.1 .0)
    }

    let signed_number = maybe_sign
        .then(digits)
        .filter(immediately_adjoining)
        .map(discard_spans);

    signed_number
        .try_map_with(move |(maybe_sign, number), extra| {
            let state: &SimpleState<NumeralMode> = extra.state();
            let mode: &NumeralMode = state.deref();
            match number.make_num(maybe_sign, mode) {
                Ok(value) => Ok(LiteralValue::from((extra.span(), script_required, value))),
                Err(e) => Err(Rich::custom(extra.span(), e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn here<'a, I>(script_required: Script) -> impl Parser<'a, I, Atom, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        Tok::Hash(script) if script == script_required => Atom::Here(script_required),
    }
}

/// TODO: redundant if we use helpers::opcode_mapping.
fn opcode_code(s: &str) -> Option<Unsigned6Bit> {
    match s {
        "IOS" => Some(u6!(0o4)),
        "JMP" => Some(u6!(0o5)),
        "JPX" => Some(u6!(0o6)),
        "JNX" => Some(u6!(0o7)),
        "AUX" => Some(u6!(0o10)),
        "RSX" => Some(u6!(0o11)),
        "SKX" => Some(u6!(0o12)),
        "REX" => Some(u6!(0o12)),
        "SEX" => Some(u6!(0o12)),
        "EXX" => Some(u6!(0o14)),
        "ADX" => Some(u6!(0o15)),
        "DPX" => Some(u6!(0o16)),
        "SKM" => Some(u6!(0o17)),
        "LDE" => Some(u6!(0o20)),
        "SPF" => Some(u6!(0o21)),
        "SPG" => Some(u6!(0o22)),
        "LDA" => Some(u6!(0o24)),
        "LDB" => Some(u6!(0o25)),
        "LDC" => Some(u6!(0o26)),
        "LDD" => Some(u6!(0o27)),
        "STE" => Some(u6!(0o30)),
        "FLF" => Some(u6!(0o31)),
        "FLG" => Some(u6!(0o32)),
        "STA" => Some(u6!(0o34)),
        "STB" => Some(u6!(0o35)),
        "STC" => Some(u6!(0o36)),
        "STD" => Some(u6!(0o37)),
        "ITE" => Some(u6!(0o40)),
        "ITA" => Some(u6!(0o41)),
        "UNA" => Some(u6!(0o42)),
        "SED" => Some(u6!(0o43)),
        "JOV" => Some(u6!(0o45)),
        "JPA" => Some(u6!(0o46)),
        "JNA" => Some(u6!(0o47)),
        "EXA" => Some(u6!(0o54)),
        "INS" => Some(u6!(0o55)),
        "COM" => Some(u6!(0o56)),
        "TSD" => Some(u6!(0o57)),
        "CYA" => Some(u6!(0o60)),
        "CYB" => Some(u6!(0o61)),
        "CAB" => Some(u6!(0o62)),
        "NOA" => Some(u6!(0o64)),
        "DSA" => Some(u6!(0o65)),
        "NAB" => Some(u6!(0o66)),
        "ADD" => Some(u6!(0o67)),
        "SCA" => Some(u6!(0o70)),
        "SCB" => Some(u6!(0o71)),
        "SAB" => Some(u6!(0o72)),
        "TLY" => Some(u6!(0o74)),
        "DIV" => Some(u6!(0o75)),
        "MUL" => Some(u6!(0o76)),
        "SUB" => Some(u6!(0o77)),
        _ => None,
    }
}

pub(super) fn opcode<'a, I>() -> impl Parser<'a, I, LiteralValue, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn opcode_to_literal(code: Unsigned6Bit, span: Span) -> LiteralValue {
        // Some opcodes automatically set the hold bit, so do that
        // here.
        let bits = Unsigned36Bit::from(code)
            .shl(24)
            .bitor(helpers::opcode_auto_hold_bit(code));
        LiteralValue::from((span, Script::Normal, bits))
    }

    symex::symex_syllable(Script::Normal)
        .filter(|mnemonic| opcode_code(mnemonic).is_some())
        .try_map_with(|mnemonic, extra| match opcode_code(mnemonic.as_str()) {
            Some(code) => Ok(opcode_to_literal(code, extra.span())),
            None => Err(Rich::custom(
                extra.span(),
                format!("'{mnemonic}' is not an opcode mnemonic"),
            )),
        })
        .labelled("opcode")
}

fn symbol<'a, I>(script_required: Script) -> impl Parser<'a, I, SymbolName, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    symex::parse_symex(script_required)
        .map(SymbolName::from)
        .labelled("symex (symbol) name")
}

fn tag_definition<'a, I>() -> impl Parser<'a, I, Tag, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    symbol(Script::Normal)
        .map_with(|name, extra| Tag {
            name,
            span: extra.span(),
        })
        .then_ignore(just(Tok::Arrow))
        .labelled("tag definition")
}

pub(super) fn operator<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Operator, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        // Solidus ("/") is used for divide.  See section 6-2.7
        // "Word Assembly" for details.
        // TODO: support subscript/superscript for '/'
        Tok::Solidus if script_required == Script::Normal => Operator::Divide,
        Tok::Plus(Script::Normal) => Operator::Add,
        // TODO: support subscript/superscript for times
        Tok::Times if script_required == Script::Normal => Operator::Multiply,
        Tok::LogicalOr(got) if got == script_required => Operator::LogicalOr,
        Tok::LogicalAnd(got) if got == script_required => Operator::LogicalAnd,
        Tok::Minus(got) if script_required == got => Operator::Subtract,
        Tok::Plus(got) if script_required == got => Operator::Add,
    }
    .labelled("arithmetic operator")
}

fn program_instruction_fragments<'srcbody, I>(
) -> impl Parser<'srcbody, I, Vec<InstructionFragment>, Extra<'srcbody>>
where
    I: Input<'srcbody, Token = Tok, Span = Span> + ValueInput<'srcbody>,
{
    recursive(move |program_instruction_fragments| {
        // Parse a sequence of values (symbolic or literal) and arithmetic
        // operators.
        //
        // BAT² is not an identifier but a sequence[1] whose value is
        // computed by OR-ing the value of the symex BAT with the value of
        // the literal "²" (which is 2<<30, or 0o20_000_000_000).  But BAT²
        // is itself not an arithmetic_expression (because there is a script
        // change).
        //
        // You could argue that (BAT²) should be parsed as an atom.  Right
        // now that doesn't work because all the elements of an expression
        // (i.e. everything within the parens) need to have the same script.
        //
        // [1] I use "sequence" in the paragraph above to avoid saying
        // "expression" or "instruction fragment".
        let arith_expr = |script_required: Script| {
            // We use recursive here to prevent the parser blowing the stack
            // when trying to parse inputs which have parentheses - that is,
            // inputs that require recursion.
            recursive(move |arithmetic_expr| {
                // Parse (E) where E is some expression.
                let parenthesised_arithmetic_expression = arithmetic_expr // this is the recursive call
                    .clone()
                    .delimited_by(
                        just(Tok::LeftParen(script_required)),
                        just(Tok::RightParen(script_required)),
                    )
                    .map(move |expr| Atom::Parens(script_required, Box::new(expr)))
                    .labelled("parenthesised arithmetic expression");

                // Parse {E} where E is some expression.  Since tags are
                // allowed inside RC-blocks, we should parse E as a
                // TaggedProgramInstruction.  But if we try to do that without
                // using recursive() we will blow the stack, unfortunately.
                let register_containing = program_instruction_fragments
                    .clone()
                    .delimited_by(just(Tok::LeftBrace), just(Tok::RightBrace))
                    .map_with(|fragments, extra| Atom::RcRef(extra.span(), fragments))
                    .labelled("RC-word");

                // Parse a literal, symbol, #, or (recursively) an expression in parentheses.
                let atom = choice((
                    literal(script_required).map(Atom::from),
                    here(script_required).map(Atom::from),
                    opcode().map(Atom::from),
                    symbol(script_required).map_with(move |name, extra| {
                        Atom::Symbol(extra.span(), script_required, name)
                    }),
                    register_containing,
                    parenthesised_arithmetic_expression,
                ))
                .boxed();

                // Parse an arithmetic operator (e.g. plus, times) followed by an atom.
                let operator_with_atom = operator(script_required).then(atom.clone());

                // An arithmetic expression is an atom followed by zero or
                // more pairs of (arithmetic operator, atom).
                atom.then(operator_with_atom.repeated().collect())
                    .map(|(head, tail)| ArithmeticExpression::with_tail(head, tail))
            })
        };

        let single_script_fragment =
            |script_required| arith_expr.clone()(script_required).map(InstructionFragment::from);

        choice((
            single_script_fragment(Script::Normal),
            single_script_fragment(Script::Super),
            single_script_fragment(Script::Sub),
            just(Tok::Asterisk).to(InstructionFragment::DeferredAddressing),
        ))
        .repeated()
        .at_least(1)
        .collect()
        .labelled("program instruction")
    })
}

/// Macro terminators are described in section 6-4.5 of the TX-2 User Handbook.
fn macro_terminator<'a, I>() -> impl Parser<'a, I, char, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // This list of 16 allowed terminators is exhaustive, see section
    // 6-4.5 of the TX-2 User Handbook.
    //
    // ☛ · = →  | ⊃ ≡ ~ < > ∩ ∪ / × ∨ ∧
    //
    // We use a centre dot for the dot symbol because otherwise the
    // low position of "." makes it look like part of a subscript.
    choice((
        just(Tok::Hand).to('☛'),
        just(Tok::Dot(Script::Normal)).to(lexer::DOT_CHAR),
        just(Tok::Equals).to('='),
        just(Tok::Arrow).to('→'),
        just(Tok::Pipe).to('|'),
        just(Tok::ProperSuperset).to('⊃'),
        just(Tok::IdenticalTo).to('≡'),
        just(Tok::Tilde).to('~'),
        just(Tok::LessThan).to('<'),
        just(Tok::GreaterThan).to('>'),
        just(Tok::Intersection).to('∩'),
        just(Tok::Union).to('∪'),
        just(Tok::Solidus).to('/'),
        just(Tok::Times).to('×'),
        just(Tok::LogicalOr(Script::Normal)).to('∨'),
        just(Tok::LogicalAnd(Script::Normal)).to('∧'),
    ))
}

fn macro_argument<'a, I>() -> impl Parser<'a, I, MacroArgument, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    (macro_terminator().then(symbol(Script::Normal))).map_with(|(terminator, symbol), extra| {
        MacroArgument {
            name: symbol,
            span: extra.span(),
            preceding_terminator: terminator,
        }
    })
}

fn macro_arguments<'a, I>() -> impl Parser<'a, I, MacroArguments, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        macro_argument()
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>()
            .map(MacroArguments::OneOrMore),
        macro_terminator().map(MacroArguments::Zero),
    ))
}

/// Macros are described in section 6-4 of the TX-2 User Handbook.
fn macro_definition<'a, I>() -> impl Parser<'a, I, MacroDefinition, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    named_metacommand(Metacommand::DefineMacro)
        .ignore_then(
            symbol(Script::Normal), // the macro's name
        )
        .then(macro_arguments())
        .then_ignore(end_of_line())
        .then(
            (statement().then_ignore(end_of_line()))
                .repeated()
                .collect::<Vec<_>>()
                .labelled("macro body"),
        )
        .then_ignore(named_metacommand(Metacommand::EndMacroDefinition))
        // We don't parse end-of-line here because all metacommands are supposed
        // to be followed by end-of-line.
        .map_with(|((name, args), body), extra| MacroDefinition {
            name,
            args,
            body,
            span: extra.span(),
        })
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Metacommand {
    Decimal,
    Octal,
    Punch,
    DefineMacro,
    EndMacroDefinition,
}

fn named_metacommand<'a, I>(which: Metacommand) -> impl Parser<'a, I, (), Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let name_match = move |actual: &str| -> bool {
        match which {
            Metacommand::Decimal => {
                matches!(actual, "DECIMAL" | "DECIMA" | "DECIM" | "DECI" | "DEC")
            }
            Metacommand::Octal => matches!(actual, "OCTAL" | "OCTA" | "OCT" | "OC"),
            Metacommand::Punch => matches!(actual, "PUNCH" | "PUNC" | "PUN" | "PU"),
            Metacommand::DefineMacro => actual == "DEF",
            Metacommand::EndMacroDefinition => matches!(actual, "EMD" | "EM"),
        }
    };

    let matching_metacommand_name = select! {
        Tok::SymexSyllable(Script::Normal, name) if name_match(name.as_str()) => (),
    };

    just([Tok::Hand, Tok::Hand])
        .ignored()
        .then_ignore(matching_metacommand_name)
}

fn metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn punch<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        // We currently have a limitation in the interpretation of
        // "AA" in the PUNCH metacommand.  The documentation clearly
        // states that this should be an honest tag.  We currently
        // accept only numeric literals.
        named_metacommand(Metacommand::Punch)
            .ignore_then(literal(Script::Normal).or_not())
            .try_map(|aa, span| match helpers::punch_address(aa) {
                Ok(punch) => Ok(ManuscriptMetaCommand::Punch(punch)),
                Err(msg) => Err(Rich::custom(span, msg)),
            })
            .labelled("PUNCH command")
    }

    fn base_change<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        choice((
            named_metacommand(Metacommand::Decimal)
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Decimal)),
            named_metacommand(Metacommand::Octal)
                .to(ManuscriptMetaCommand::BaseChange(NumeralMode::Octal)),
        ))
        .labelled("base-change metacommand")
    }

    choice((
        base_change(),
        punch(),
        macro_definition().map(ManuscriptMetaCommand::Macro),
    ))
    .labelled("metacommand")
}

fn untagged_program_instruction<'a, I>() -> impl Parser<'a, I, UntaggedProgramInstruction, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let maybe_hold = choice((
        one_of(Tok::Hold).to(HoldBit::Hold),
        just(Tok::NotHold).to(HoldBit::NotHold),
    ))
    .or_not()
    .labelled("instruction hold bit");
    maybe_hold.then(program_instruction_fragments()).map_with(
        |(maybe_hold, parts): (Option<HoldBit>, Vec<InstructionFragment>), extra| {
            UntaggedProgramInstruction {
                span: extra.span(),
                holdbit: maybe_hold.unwrap_or(HoldBit::Unspecified),
                parts,
            }
        },
    )
}

fn tagged_program_instruction<'a, I>() -> impl Parser<'a, I, TaggedProgramInstruction, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
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

fn statement<'a, I>() -> impl Parser<'a, I, Statement, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    /// Assginments are called "equalities" in the TX-2 Users Handbook.
    /// See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
    /// AUTOMATIC ASSIGNMENT".
    fn assignment<'a, I>() -> impl Parser<'a, I, (SymbolName, UntaggedProgramInstruction), Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        (symex::parse_symex(Script::Normal)
            .then_ignore(just(Tok::Equals))
            .then(untagged_program_instruction()))
        .labelled("equality (assignment)")
    }

    choice((
        // We have to parse an assignment first here, in order to
        // accept "FOO=2" as an assignment rather than the instruction
        // fragment "FOO" followed by a syntax error.
        assignment().map_with(|(sym, inst), extra| Statement::Assignment(extra.span(), sym, inst)),
        tagged_program_instruction().map(Statement::Instruction),
    ))
}

fn manuscript_line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn execute_metacommand(state: &mut NumeralMode, cmd: &ManuscriptMetaCommand) {
        match cmd {
            ManuscriptMetaCommand::Punch(_) | ManuscriptMetaCommand::Macro(_) => {
                // Instead of executing this metacommand as we parse it,
                // we simply return it as part of the parser output, and
                // it is executed by the driver.
            }
            ManuscriptMetaCommand::BaseChange(new_base) => state.set_numeral_mode(*new_base),
        }
    }

    fn parse_and_execute_metacommand<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        metacommand()
            .map_with(|cmd, extra| {
                execute_metacommand(extra.state(), &cmd);
                ManuscriptLine::MetaCommand(cmd)
            })
            .labelled("metacommand")
    }

    fn build_code_line(parts: (Option<Origin>, Statement)) -> ManuscriptLine {
        ManuscriptLine::Code(parts.0, parts.1)
    }

    fn line<'a, I>() -> impl Parser<'a, I, ManuscriptLine, Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        fn origin<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a>>
        where
            I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
        {
            /// An address expression is a literal value or a symex.  That is I
            /// think it's not required that an arithmetic expression
            /// (e.g. "5+BAR") be accepted in an origin notation (such as
            /// "<something>|").
            fn literal_address_expression<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a>>
            where
                I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
            {
                // We should eventually support symexes here.
                literal(Script::Normal)
                    .try_map(|lit, span| match Address::try_from(lit.value()) {
                        Ok(addr) => Ok(Origin::Literal(span, addr)),
                        Err(e) => Err(Rich::custom(span, format!("not a valid address: {e}"))),
                    })
                    .labelled("literal address expression")
            }

            fn symbolic_address_expression<'a, I>() -> impl Parser<'a, I, Origin, Extra<'a>>
            where
                I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
            {
                symbol(Script::Normal)
                    .map_with(|sym, extra| Origin::Symbolic(extra.span(), sym))
                    .labelled("symbolic address expression")
            }

            // An origin specification is an expression followed by a
            // (normal-case) pipe symbol.
            choice((literal_address_expression(), symbolic_address_expression()))
                .then_ignore(just(Tok::Pipe))
                .labelled("origin specification")
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

fn end_of_line<'a, I>() -> impl Parser<'a, I, (), Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span>,
{
    let one_end_of_line = just(Tok::Newline).labelled("end-of-line").ignored();

    one_end_of_line
        .repeated()
        .at_least(1)
        .ignored()
        .labelled("comment or end-of-line")
}

fn terminated_manuscript_line<'a, I>() -> impl Parser<'a, I, Option<ManuscriptLine>, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // If we support INSERT, DELETE, REPLACE, we will need to
    // separate the processing of the metacommands and the
    // generation of the assembled code.
    manuscript_line().or_not().then_ignore(end_of_line())
}

pub(crate) fn source_file<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // Parse a manuscript (which is a sequence of metacommands, macros
    // and assembly-language instructions).
    fn source_file_as_blocks<'a, I>() -> impl Parser<'a, I, SourceFile, Extra<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        terminated_manuscript_line().repeated().collect().map(
            |lines: Vec<Option<ManuscriptLine>>| {
                // Filter out empty lines.
                let lines: Vec<ManuscriptLine> = lines.into_iter().flatten().collect();
                let (blocks, macros, punch) = helpers::manuscript_lines_to_blocks(lines);
                SourceFile {
                    blocks,
                    macros,
                    punch,
                }
            },
        )
    }
    source_file_as_blocks()
}

type Mig<I, O> = chumsky::input::MappedInput<
    Tok,
    SimpleSpan,
    chumsky::input::Stream<std::vec::IntoIter<(Tok, SimpleSpan)>>,
    fn(I) -> O,
>;
pub(crate) type Mi = Mig<(Tok, SimpleSpan), (Tok, SimpleSpan)>;

pub(crate) fn tokenize_and_parse_with<'a, P, T>(
    input: &'a str,
    setup: fn(&mut NumeralMode),
    parser: P,
) -> (Option<T>, Vec<Rich<'a, Tok>>)
where
    P: Parser<'a, Mi, T, Extra<'a>>,
{
    let mut state = SimpleState::from(NumeralMode::default());
    setup(&mut state);

    // These conversions are adapted from the Logos example in the
    // Chumsky documentation.
    let scanner = lexer::Lexer::new(input).spanned();
    let tokens: Vec<(Tok, SimpleSpan)> = scanner
        .map(
            |item: (Result<Tok, Unrecognised>, Range<usize>)| -> (Tok, Span) {
                match item {
                    (Ok(tok), span) => {
                        // Turn the `Range<usize>` spans logos gives us into
                        // chumsky's `SimpleSpan` via `Into`, because it's
                        // easier to work with
                        (tok, span.into())
                    }
                    (Err(e), span) => {
                        // Convert logos errors into tokens. We want parsing to
                        // be recoverable and not fail at the lexing stage, so we
                        // have a dedicated `Token::Error` variant that
                        // represents a token error that was previously
                        // encountered
                        (Tok::Error(e.to_string()), span.into())
                    }
                }
            },
        )
        .collect();
    let end_span: SimpleSpan = SimpleSpan::new(
        0,
        tokens.iter().map(|(_, span)| span.end).max().unwrap_or(0),
    );
    let token_stream: Mi = Stream::from_iter(tokens).map(end_span, |unchanged| unchanged);
    parser
        .parse_with_state(token_stream, &mut state)
        .into_output_errors()
}

pub(crate) fn parse_source_file(
    source_file_body: &str,
    setup: fn(&mut NumeralMode),
) -> (Option<SourceFile>, Vec<Rich<'_, Tok>>) {
    let parser = source_file();
    tokenize_and_parse_with(source_file_body, setup, parser)
}

// Local Variables:
// mode: rustic
// lsp-rust-analyzer-server-display-inlay-hints: nil
// End:
