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
use chumsky::prelude::{choice, just, one_of, recursive, Input, IterParser, Recursive, SimpleSpan};
use chumsky::select;
use chumsky::Boxed;
use chumsky::Parser;

use super::ast::*;
use super::glyph::Unrecognised;
use super::lexer::{self};
use super::span::*;
use super::state::NumeralMode;
use super::symbol::{SymbolName, SymbolOrHere};
use base::charset::Script;
use base::prelude::*;
use helpers::Sign;
use symex::SymexSyllableRule;

pub(crate) type Extra<'a> = Full<Rich<'a, lexer::Token>, SimpleState<NumeralMode>, ()>;
use lexer::Token as Tok;

fn maybe_sign<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Option<(Sign, Span)>, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        just(Tok::Plus(script_required)).to(Sign::Plus),
        just(Tok::Minus(script_required)).to(Sign::Minus),
    ))
    .map_with(|maybe_sign, extra| (maybe_sign, extra.span()))
    .or_not()
}

fn literal<'a, I>(script_required: Script) -> impl Parser<'a, I, LiteralValue, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let digits = select! {
        Tok::Digits(script, n) if script == script_required => n,
    };

    digits
        .try_map_with(move |digits_token_payload, extra| {
            let state: &SimpleState<NumeralMode> = extra.state();
            let mode: &NumeralMode = state.deref();
            match digits_token_payload.make_num(None, mode) {
                Ok(value) => Ok(LiteralValue::from((extra.span(), script_required, value))),
                Err(e) => Err(Rich::custom(extra.span(), e.to_string())),
            }
        })
        .labelled("numeric literal")
}

fn here<'a, I>(script_required: Script) -> impl Parser<'a, I, SymbolOrHere, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        Tok::Hash(script) if script == script_required => SymbolOrHere::Here,
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

pub(super) fn symbol_or_literal<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, SymbolOrLiteral, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        literal(script_required).map(SymbolOrLiteral::Literal),
        symex::symex_syllable(script_required).map_with(move |name, extra| {
            SymbolOrLiteral::Symbol(script_required, SymbolName::from(name), extra.span())
        }),
    ))
    .labelled(match script_required {
        Script::Super => "superscript single-syllable symbol or literal",
        Script::Normal => "single-syllable symbol or literal",
        Script::Sub => "subscript single-syllable symbol or literal",
    })
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

fn named_symbol<'a, I>(
    rule: SymexSyllableRule,
    script_required: Script,
) -> impl Parser<'a, I, SymbolName, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    symex::parse_symex(rule, script_required)
}

fn named_symbol_or_here<'a, I>(
    rule: SymexSyllableRule,
    script_required: Script,
) -> impl Parser<'a, I, SymbolOrHere, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        here(script_required),
        named_symbol(rule, script_required).map(SymbolOrHere::Named),
    ))
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
        Tok::Solidus(script) if script_required == script => Operator::Divide,
        Tok::Plus(Script::Normal) => Operator::Add,
        Tok::Times(got) if got == script_required => Operator::Multiply,
        Tok::LogicalOr(got) if got == script_required => Operator::LogicalOr,
        Tok::LogicalAnd(got) if got == script_required => Operator::LogicalAnd,
        Tok::Minus(got) if script_required == got => Operator::Subtract,
        Tok::Plus(got) if script_required == got => Operator::Add,
    }
    .labelled("arithmetic operator")
}

fn asterisk_indirection_fragment<'srcbody, I>(
) -> impl Parser<'srcbody, I, InstructionFragment, Extra<'srcbody>> + Clone
where
    I: Input<'srcbody, Token = Tok, Span = Span> + ValueInput<'srcbody>,
{
    just(Tok::Asterisk(Script::Normal)).to(InstructionFragment::DeferredAddressing)
}

/// The pipe construct is described in section 6-2.8 "SPECIAL SYMBOLS"
/// of the Users Handbook.
///
/// "ADXₚ|ₜQ" should be equivalent to "ADXₚ{Qₜ}*".  So during
/// evaluation we will need to generate an RC-word containing Qₜ.
fn make_pipe_construct(
    ((p_index, t), (qfrag, qspan)): (
        (SymbolOrLiteral, SymbolOrLiteral),
        (InstructionFragment, Span),
    ),
) -> InstructionFragment {
    // The variable names here are taken from the example in the
    // documentation comment.
    InstructionFragment::PipeConstruct {
        index: p_index,
        rc_word_span: qspan,
        rc_word_value: Box::new((qfrag, Atom::from(t))),
    }
}

/// Macro terminators are described in section 6-4.5 of the TX-2 User Handbook.
fn macro_terminator<'a, I>() -> impl Parser<'a, I, char, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // This list of 16 allowed terminators is exhaustive, see section
    // 6-4.5 of the TX-2 User Handbook.
    //
    // ☛ , = →  | ⊃ ≡ ~ < > ∩ ∪ / × ∨ ∧
    //
    // The second symbol, in my scanned copy of the Users Handbook
    // (page 6-31 of the Nov 1963 Users Handbook), looks like either a
    // comma or a dot/full-stop/period.  Since a dot is valid in a
    // symex name, and because the symbol seems to be taller than it
    // is wide, I'm going to assume it is a comma.
    //
    // They are actually hard to distinguish in the copy of the Users
    // Handbook I have.  But, looking at page 011 of Leonard
    // Kleinrock's listing for his network simulator, the `HP OS`
    // macro is definitely using as a separator a symbol that lives on
    // the line.  If you look a little further below on the same
    // page, the third instruction in the body of the `MV MX` macro
    // body contains both a dot and a comma.  The dot is definitely
    // above the line and looks rounder.  So I conclude that the
    // separator character is a comma.
    choice((
        just(Tok::Hand(Script::Normal)).to('☛'),
        just(Tok::Comma(Script::Normal)).to(','),
        just(Tok::Equals(Script::Normal)).to('='),
        just(Tok::Arrow(Script::Normal)).to('→'),
        just(Tok::Pipe(Script::Normal)).to('|'),
        just(Tok::ProperSuperset(Script::Normal)).to('⊃'),
        just(Tok::IdenticalTo(Script::Normal)).to('≡'),
        just(Tok::Tilde(Script::Normal)).to('~'),
        just(Tok::LessThan(Script::Normal)).to('<'),
        just(Tok::GreaterThan(Script::Normal)).to('>'),
        just(Tok::Intersection(Script::Normal)).to('∩'),
        just(Tok::Union(Script::Normal)).to('∪'),
        just(Tok::Solidus(Script::Normal)).to('/'),
        just(Tok::Times(Script::Normal)).to('×'),
        just(Tok::LogicalOr(Script::Normal)).to('∨'),
        just(Tok::LogicalAnd(Script::Normal)).to('∧'),
    ))
    .labelled("macro terminator")
}

fn macro_argument<'a, I>() -> impl Parser<'a, I, MacroArgument, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // The TX-2 Users Handbook section 6-4.4 ("DUMMY PARAMETERS")
    // doesn't disallow spaces in macro argument names.
    (macro_terminator().then(named_symbol(SymexSyllableRule::Multiple, Script::Normal))).map_with(
        |(terminator, symbol), extra| MacroArgument {
            name: symbol,
            span: extra.span(),
            preceding_terminator: terminator,
        },
    )
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
            named_symbol(SymexSyllableRule::Multiple, Script::Normal).labelled("macro name"), // the macro's name (# is not allowed)
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

    just([Tok::Hand(Script::Normal), Tok::Hand(Script::Normal)])
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

pub(crate) fn instructions_with_comma_counts<I>(it: I) -> Vec<CommaDelimitedInstruction>
where
    I: Iterator<Item = CommasOrInstruction>,
{
    use CommasOrInstruction::*;
    let mut it = it.peekable();

    /// Fold operation which estabishes an alternating pattern of
    /// commas and instructions.
    ///
    /// Invariant: acc is non-empty, begins and ends with C(_)
    /// and does not contain a consecutive pair of C(_) or a
    /// consecutive pair of Inst(_).
    fn fold_step(
        mut acc: Vec<CommasOrInstruction>,
        item: CommasOrInstruction,
    ) -> Vec<CommasOrInstruction> {
        fn null_instruction(span: Span) -> UntaggedProgramInstruction {
            UntaggedProgramInstruction {
                span,
                holdbit: HoldBit::Unspecified,
                inst: InstructionFragment::from(ArithmeticExpression::from(Atom::Literal(
                    LiteralValue::from((span, Script::Normal, Unsigned36Bit::ZERO)),
                ))),
            }
        }

        match acc.last_mut() {
            Some(CommasOrInstruction::C(tail_comma)) => match item {
                CommasOrInstruction::C(maybe_commas) => {
                    if tail_comma.is_none() {
                        *tail_comma = maybe_commas;
                    } else {
                        let null_inst_span: Span = match (tail_comma, &maybe_commas) {
                            (_, Some(ic)) => span(ic.span().start..ic.span().start),
                            (Some(tc), _) => span(tc.span().start..tc.span().start),
                            (None, None) => {
                                unreachable!("should be no need to interpose a null instruction between two instances of zero commas");
                            }
                        };
                        dbg!(&null_inst_span);
                        acc.push(CommasOrInstruction::I(null_instruction(null_inst_span)));
                        acc.push(CommasOrInstruction::C(maybe_commas));
                    }
                }
                CommasOrInstruction::I(inst) => {
                    acc.push(CommasOrInstruction::I(inst));
                    acc.push(CommasOrInstruction::C(None));
                }
            },
            Some(I(_)) => unreachable!("invariant was broken"),
            None => unreachable!("invariant was not established"),
        }
        assert!(matches!(acc.first(), Some(C(_))));
        assert!(matches!(acc.last(), Some(C(_))));
        acc
    }

    let initial_accumulator: Vec<CommasOrInstruction> = vec![CommasOrInstruction::C({
        match it.peek() {
            None => {
                return Vec::new();
            }
            Some(I(_)) => None,
            Some(C(maybe_commas)) => {
                let c = maybe_commas.clone();
                it.next();
                c
            }
        }
    })];

    let tmp = it.fold(initial_accumulator, fold_step);
    let mut output: Vec<CommaDelimitedInstruction> = Vec::with_capacity(tmp.len() / 2 + 1);
    let mut it = tmp.into_iter().peekable();
    loop {
        let maybe_before_count = it.next();
        let maybe_inst = it.next();
        match (maybe_before_count, maybe_inst) {
            (None, _) => {
                break;
            }
            (Some(C(before_commas)), Some(I(inst))) => {
                let after_commas: Option<Commas> = match it.peek() {
                    Some(CommasOrInstruction::C(commas)) => commas.clone(),
                    None => None,
                    Some(CommasOrInstruction::I(_)) => {
                        unreachable!("fold_step did not maintain its invariant")
                    }
                };
                output.push(CommaDelimitedInstruction::new(
                    before_commas,
                    inst,
                    after_commas,
                ));
            }
            (Some(C(_)), None) => {
                // No instructions in the input.
                break;
            }
            (Some(I(_)), _) | (Some(C(_)), Some(C(_))) => {
                unreachable!("fold_step did not maintain its invariant");
            }
        }
    }
    output
}

fn tag_definition<'a, I>() -> impl Parser<'a, I, Tag, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    named_symbol(SymexSyllableRule::Multiple, Script::Normal)
        .map_with(|name, extra| Tag {
            name,
            span: extra.span(),
        })
        .then_ignore(just(Tok::Arrow(Script::Normal)))
        .labelled("tag definition")
}

fn commas<'a, I>() -> impl Parser<'a, I, Commas, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    just(Tok::Comma(Script::Normal))
        .repeated()
        .at_least(1)
        .at_most(3)
        .count()
        .map_with(|count, extra| {
            let span = extra.span();
            match count {
                1 => Commas::One(span),
                2 => Commas::Two(span),
                3 => Commas::Three(span),
                _ => unreachable!(),
            }
        })
}

fn maybe_hold<'a, I>() -> impl Parser<'a, I, Option<HoldBit>, Extra<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        one_of(Tok::Hold).to(HoldBit::Hold),
        just(Tok::NotHold).to(HoldBit::NotHold),
    ))
    .or_not()
    .labelled("instruction hold bit")
}

struct Grammar<'a, 'b, I>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    statement: Boxed<'a, 'b, I, Statement, Extra<'a>>,
    #[cfg(test)]
    normal_arithmetic_expression_allowing_spaces: Boxed<'a, 'b, I, ArithmeticExpression, Extra<'a>>,
    #[cfg(test)]
    subscript_arithmetic_expression_allowing_spaces:
        Boxed<'a, 'b, I, ArithmeticExpression, Extra<'a>>,
    #[cfg(test)]
    superscript_arithmetic_expression_allowing_spaces:
        Boxed<'a, 'b, I, ArithmeticExpression, Extra<'a>>,
    #[cfg(test)]
    instruction_fragment: Boxed<'a, 'b, I, InstructionFragment, Extra<'a>>,
}

fn grammar<'a: 'b, 'b, I>() -> Grammar<'a, 'b, I>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let mut comma_delimited_instructions = Recursive::declare();
    let tagged_program_instruction = tag_definition()
        .or_not()
        .then(comma_delimited_instructions.clone())
        .map(
            |(tag, instructions): (Option<Tag>, Vec<CommaDelimitedInstruction>)| {
                TaggedProgramInstruction { tag, instructions }
            },
        )
        .labelled(
            "optional tag definition followed by a (possibly comma-delimited) program instructions",
        );

    // Parse {E} where E is some expression.  Since tags are
    // allowed inside RC-blocks, we should parse E as a
    // TaggedProgramInstruction.  But if we try to do that without
    // using recursive() we will blow the stack, unfortunately.
    let register_containing = tagged_program_instruction
        .clone()
        .delimited_by(
            just(Tok::LeftBrace(Script::Normal)),
            just(Tok::RightBrace(Script::Normal)),
        )
        .map_with(|tagged_instruction, extra| Atom::RcRef(extra.span(), vec![tagged_instruction]))
        .labelled("RC-word");

    let arith_expr = |allow_spaces: bool, script_required: Script| {
        {
            let symex_syllable_rule = if allow_spaces {
                SymexSyllableRule::Multiple
            } else {
                SymexSyllableRule::OneOnly
            };
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
                    .map_with(move |expr, extra| {
                        Atom::Parens(extra.span(), script_required, Box::new(expr))
                    })
                    .labelled("parenthesised arithmetic expression");

                // Parse a literal, symbol, #, or (recursively) an expression in parentheses.
                let naked_atom = choice((
                    literal(script_required).map(Atom::from),
                    opcode().map(Atom::from),
                    named_symbol_or_here(symex_syllable_rule, script_required).map_with(
                        move |symbol_or_here, extra| {
                            Atom::Symbol(extra.span(), script_required, symbol_or_here)
                        },
                    ),
                    register_containing,
                    parenthesised_arithmetic_expression,
                ))
                .boxed();

                let signed_atom = maybe_sign(script_required).then(naked_atom).map_with(
                    |(possible_sign, magnitude), extra| SignedAtom {
                        span: extra.span(),
                        negated: matches!(possible_sign, Some((Sign::Minus, _))),
                        magnitude,
                    },
                );

                // Parse an arithmetic operator (e.g. plus, times) followed by an atom.
                let operator_with_signed_atom = operator(script_required).then(signed_atom.clone());

                // An arithmetic expression is a signed atom followed by zero or
                // more pairs of (arithmetic operator, signed atom).
                signed_atom
                    .then(operator_with_signed_atom.repeated().collect())
                    .map(|(head, tail)| ArithmeticExpression::with_tail(head, tail))
            })
        }
        .labelled("arithmetic expression")
    };

    // Parse a values (symbolic or literal) or arithmetic expression.
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
    let program_instruction_fragment = recursive(|program_instruction_fragment| {
        // Parse the pipe-construct described in the User Handbook
        // section 2-2.8 "SPECIAL SYMBOLS" as "ₚ|ₜ" (though in reality
        // the pipe should also be subscript and in their example they
        // use a subscript q).
        //
        // The Handbook is not explicit on whether the "ₚ" or "ₜ" can
        // contain spaces.  We will assume not, for simplicity (at
        // least for the time being).
        //
        // "ADXₚ|ₜQ" should be equivalent to ADXₚ{Qₜ}*.  So we need to
        // generate an RC-word containing Qₜ.
        let spanned_fragment = program_instruction_fragment // this is Q
            .clone()
            .map_with(|frag, extra| (frag, extra.span()));
        let pipe_construct = (symbol_or_literal(Script::Sub) // this is p
            .then_ignore(just(Tok::Pipe(Script::Sub)))
            .then(
                symbol_or_literal(Script::Sub), // this is t
            )
            .then(spanned_fragment))
        .map(make_pipe_construct)
        .labelled("pipe construct");

        let single_script_fragment = |script_required| {
            arith_expr.clone()(true, script_required).map(InstructionFragment::from)
        };

        // A configuration syllable is not permitted to contain spaces
        // (per section 6-1.2 "INSTRUCTION WORDS" of the Users
        // Handbook).  So we need to prevent symex matching accepting
        // spaces.
        let config_value = choice((
            just(Tok::DoublePipe(Script::Normal)).ignore_then(
                arith_expr.clone()(false, Script::Normal).map(|expr| ConfigValue {
                    already_superscript: false,
                    expr,
                }),
            ),
            arith_expr.clone()(false, Script::Super).map(|expr| ConfigValue {
                already_superscript: true,
                expr,
            }),
        ))
        .map(InstructionFragment::Config)
        .labelled("configuration value");

        choice((
            pipe_construct,
            single_script_fragment(Script::Normal),
            single_script_fragment(Script::Sub),
            asterisk_indirection_fragment(),
            config_value,
        ))
        .labelled("program instruction")
    });

    comma_delimited_instructions.define({
        let untagged_program_instruction = maybe_hold()
            .then(program_instruction_fragment.clone())
            .map_with(
                |(maybe_hold, inst): (Option<HoldBit>, InstructionFragment), extra| {
                    UntaggedProgramInstruction {
                        span: extra.span(),
                        holdbit: maybe_hold.unwrap_or(HoldBit::Unspecified),
                        inst,
                    }
                },
            );

        choice((
            commas().map(|c| CommasOrInstruction::C(Some(c))),
            untagged_program_instruction
                .clone()
                .map(CommasOrInstruction::I),
        ))
        .repeated()
        .at_least(1)
        .collect::<Vec<CommasOrInstruction>>()
        .map(|ci_vec| instructions_with_comma_counts(ci_vec.into_iter()))
    });

    // Assginments are called "equalities" in the TX-2 Users Handbook.
    // See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
    // AUTOMATIC ASSIGNMENT".
    let assignment = (symex::parse_symex(SymexSyllableRule::Multiple, Script::Normal)
        .then_ignore(just(Tok::Equals(Script::Normal)))
        .then(
            comma_delimited_instructions
                .clone()
                .map(EqualityValue::from),
        ))
    .labelled("equality (assignment)");

    let stmt = choice((
        // We have to parse an assignment first here, in order to
        // accept "FOO=2" as an assignment rather than the instruction
        // fragment "FOO" followed by a syntax error.
        assignment
            .clone()
            .map_with(|(sym, inst), extra| Statement::Assignment(extra.span(), sym, inst)),
        tagged_program_instruction
            .clone()
            .map(Statement::Instruction),
    ));

    #[cfg(test)]
    const ALLOW_SPACES: bool = true;

    Grammar {
        statement: stmt.boxed(),
        #[cfg(test)]
        normal_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Normal,
        )
        .boxed(),
        #[cfg(test)]
        superscript_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Super,
        )
        .boxed(),
        #[cfg(test)]
        subscript_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Sub,
        )
        .boxed(),
        #[cfg(test)]
        instruction_fragment: program_instruction_fragment.boxed(),
    }
}

fn statement<'a, I>() -> impl Parser<'a, I, Statement, Extra<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    grammar().statement
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
                named_symbol(SymexSyllableRule::Multiple, Script::Normal)
                    .map_with(|name, extra| Origin::Symbolic(extra.span(), name))
                    .labelled("symbolic address expression")
            }

            // An origin specification is an expression followed by a
            // (normal-case) pipe symbol.
            choice((literal_address_expression(), symbolic_address_expression()))
                .then_ignore(just(Tok::Pipe(Script::Normal)))
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
                    (Ok(Tok::Tab), span) => {
                        // The basic problem here is that the TX-2's
                        // M4 assembler allows a space to occur in the
                        // middle of a symex.  We implement this in
                        // the parser by returning the individual
                        // parts from the lexer and having the parser
                        // join them together.  The lexer doesn't
                        // return spaces.  In order to prevent the
                        // parser joining together "XY\tZ" in a
                        // similar way we would need to return TAB as
                        // a lexeme.  The problem with doing that
                        // though is that the parser would have to
                        // permit the TAB token between regular
                        // tokens everywhere in the grammar except
                        // between two symex components.  That would
                        // make the grammar difficult to maintain (and
                        // difficult to specify without bugs).
                        let long_msg: String = concat!(
                            "Please do not use the TAB character. ",
                            "The differences between the M4 assembler's interpretation of tab and its interpreation of the space ",
                            "characer are complex, and these are not fully implemented.  If you want to ",
                            "prevent two adjacent symexes being joined together, please use parentheses ",
                            "or an explicit '+' operation instead.  That is, use (A)(B) or A+B instead of A<tab>B. ",
                            "If you intended to simply use TAB to produce some particular code layout, please ",
                            "use spaces instead.",
                            // Also, Winnie was right.
                        ).to_string();
                        (Tok::Error(long_msg), span.into())
                    }
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
