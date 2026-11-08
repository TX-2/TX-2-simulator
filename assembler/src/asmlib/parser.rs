//! Turn a sequence of input tokens into a data structure representing
//! it.
//!
//! This data structure isn't a tree, because the logical
//! structure of a TX-2 assembly-language program isn't tree-like.
use std::{
    collections::BTreeMap,
    collections::BTreeSet,
    fmt::Debug,
    ops::{BitOr, Range, Shl},
};

pub(crate) mod helpers;
mod macros;
mod symex;

#[cfg(test)]
mod tests;

use chumsky::error::Rich;
use chumsky::extension::v1::Ext;
use chumsky::extra::{Full, ParserExtra};
use chumsky::input::{Emitter, MapExtra, Stream, ValueInput};

use chumsky::Boxed;
use chumsky::Parser;
use chumsky::prelude::{Input, IterParser, Recursive, SimpleSpan, choice, just, one_of, recursive};
use chumsky::select;

use crate::collections::OneOrMore;

use super::ast::{
    ArithmeticExpression, Atom, CommaDelimitedFragment, Commas, CommasOrInstruction, ConfigValue,
    Equality, EqualityValue, FragmentWithHold, HoldBit, InstructionFragment, LiteralValue,
    Operator, Origin, RegisterContaining, RegistersContaining, SignedAtom, SpannedSymbolOrLiteral,
    SymbolOrLiteral, Tag, TaggedProgramInstruction, UntaggedProgramInstruction,
};
use super::lexer::{self};
use super::manuscript::{
    MacroBody, MacroDefinition, ManuscriptLine, ManuscriptMetaCommand, SourceFile,
    manuscript_lines_to_source_file,
};
use super::span::{Span, Spanned, span};
use super::state::{NumeralMode, State};
use super::symbol::SymbolName;
use base::charset::Script;
use base::prelude::*;
use helpers::Sign;
use symex::SymexSyllableRule;

pub(crate) type ExtraWithoutContext<'a> = Full<Rich<'a, lexer::Token>, State<'a>, ()>;

use lexer::Token as Tok;

fn maybe_sign<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Option<(Sign, Span)>, ExtraWithoutContext<'a>> + Clone
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

#[derive(Debug, PartialEq, Eq, Clone)]
enum BitDesignatorValidation {
    Good(LiteralValue),
    Suspect(u8, u8, LiteralValue),
}

fn make_bit_designator_literal(
    script: Script,
    quarter: u8,
    bitnum: u8,
    span: Span,
) -> BitDesignatorValidation {
    fn build(q: u64, b: u64) -> Unsigned36Bit {
        // When used as a subscript, the quarter number goes into bits
        // 3.6-3.5 (bits 23,22).  The bit number goes into bits
        // 3.4-3.1 (bits 21-18).  However, subscript values are
        // shifted left by 18 bits.  Meaning, if this is used as a
        // normal-script value, it should not be shifted.
        let qmod4: u64 = q % 4_u64;
        Unsigned36Bit::ZERO.bitor(qmod4.shl(4_u32).bitor(b))
    }
    // Apparently-invalid bit designators should still be accepted.
    // See for example the description of the SKM instruction (in
    // chapter 3 of the Users Handbook which explains what the machine
    // does with invalid bit designators.  See also the example in the
    // table in section 6-2.4 of the Users Handbook.
    //
    // So we arrange to issue a warning message for this case.
    let value = LiteralValue::from((span, script, build(quarter.into(), bitnum.into())));
    match (quarter, bitnum) {
        (1..=4, 1..=9) | (4, 10) => BitDesignatorValidation::Good(value),
        _ => BitDesignatorValidation::Suspect(quarter, bitnum, value),
    }
}

// Abbreviations for types that would otherwise be cumbersome.
pub(crate) type MyError<'a, I> = <chumsky::extra::Full<
    chumsky::error::Rich<'a, lexer::Token>,
    State<'a>,
    (),
> as ParserExtra<'a, I>>::Error;
type MyEmitter<'a, I> = Emitter<MyError<'a, I>>;
type MyErrorVec<'src> = Vec<chumsky::error::Rich<'src, lexer::Token>>;

fn warn_bad_bitpos<'src, I>(
    validated: BitDesignatorValidation,
    extra: &mut MapExtra<'src, '_, I, ExtraWithoutContext<'src>>,
    emitter: &mut MyEmitter<'src, I>,
) -> LiteralValue
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    match validated {
        // This is a warning message only, because it's
        // allowed to specify a nonexistent bit position (see
        // description of SKM instruction).
        BitDesignatorValidation::Suspect(q, b, literal) => {
            emitter.emit(Rich::custom(
                extra.span(),
                format!("bit position {q}\u{00B7}{b} does not exist"),
            ));
            literal
        }
        BitDesignatorValidation::Good(literal) => literal,
    }
}

fn bit_selector<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, LiteralValue, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        Tok::BitPosition(script, quarter, bits) if script == script_required => (quarter, bits)
    }
    .try_map_with(move |(quarter, bit), extra| {
        // Bit designators are always in decimal.  They end up in the "j bits" of the instruction word (bits 3.6 to 3.1).
        // This is described in the Users Handbook on page 3-34 (in the description of the SKM instruction)
        match quarter.as_str().parse::<u8>() {
            Err(_) => Err(Rich::custom(
                extra.span(),
                format!("quarter {quarter} is not a valid decimal number"),
            )),
            Ok(q) => match bit.as_str().parse::<u8>() {
                Ok(bit) => Ok(make_bit_designator_literal(
                    script_required,
                    q,
                    bit,
                    extra.span(),
                )),
                Err(_) => Err(Rich::custom(
                    extra.span(),
                    format!("bit position {bit} is not a valid decimal number"),
                )),
            },
        }
    })
    .validate(warn_bad_bitpos)
}

fn literal<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, LiteralValue, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let plain_literal = {
        let digits = select! {
            Tok::Digits(script, n) if script == script_required => n,
        };

        digits.try_map_with(move |digits_token_payload, extra| {
            let state: &State = extra.state();
            let mode: NumeralMode = state.numeral_mode;
            match digits_token_payload.make_num(mode) {
                Ok(value) => Ok(LiteralValue::from((extra.span(), script_required, value))),
                Err(e) => Err(Rich::custom(extra.span(), e.to_string())),
            }
        })
    };
    choice((bit_selector(script_required), plain_literal)).labelled("numeric literal")
}

fn here<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, SymbolOrLiteral, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    select! {
        Tok::Hash(script) if script == script_required => (),
    }
    .map_with(move |(), extra| SymbolOrLiteral::Here(script_required, extra.span()))
}

fn opcode_code(s: &str) -> Option<(Unsigned5Bit, Unsigned6Bit)> {
    match s {
        "IOS" => Some((u5!(0o00), u6!(0o04))),
        "JMP" => Some((u5!(0o00), u6!(0o05))),
        "BRC" => Some((u5!(0o01), u6!(0o05))),
        "JPS" => Some((u5!(0o02), u6!(0o05))),
        "BRS" => Some((u5!(0o03), u6!(0o05))),
        "JPQ" => Some((u5!(0o14), u6!(0o05))),
        "BPQ" => Some((u5!(0o15), u6!(0o05))),
        "JES" => Some((u5!(0o16), u6!(0o05))),
        "JPD" => Some((u5!(0o20), u6!(0o05))),
        "BRD" => Some((u5!(0o21), u6!(0o05))),
        "JDS" => Some((u5!(0o22), u6!(0o05))),
        "BDS" => Some((u5!(0o23), u6!(0o05))),
        "JPX" => Some((u5!(0o00), u6!(0o06))),
        "JNX" => Some((u5!(0o00), u6!(0o07))),
        "AUX" => Some((u5!(0o00), u6!(0o10))),
        "RSX" => Some((u5!(0o00), u6!(0o11))),
        "SKX" | "REX" | "SEX" => Some((u5!(0o00), u6!(0o12))),
        "INX" => Some((u5!(0o02), u6!(0o12))),
        "DEX" => Some((u5!(0o03), u6!(0o12))),
        "SXD" => Some((u5!(0o04), u6!(0o12))),
        "SXL" => Some((u5!(0o06), u6!(0o12))),
        "SXG" => Some((u5!(0o07), u6!(0o12))),
        "RXF" => Some((u5!(0o10), u6!(0o12))),
        "RXD" => Some((u5!(0o20), u6!(0o12))),
        "RFD" => Some((u5!(0o30), u6!(0o12))),
        "EXX" => Some((u5!(0o00), u6!(0o14))),
        "ADX" => Some((u5!(0o00), u6!(0o15))),
        "DPX" => Some((u5!(0o00), u6!(0o16))),
        "SKM" => Some((u5!(0o00), u6!(0o17))),
        "MKC" => Some((u5!(0o01), u6!(0o17))),
        "MKZ" => Some((u5!(0o02), u6!(0o17))),
        "MKN" => Some((u5!(0o03), u6!(0o17))),
        "SKU" => Some((u5!(0o10), u6!(0o17))),
        "SUC" => Some((u5!(0o11), u6!(0o17))),
        "SUZ" => Some((u5!(0o12), u6!(0o17))),
        "SUN" => Some((u5!(0o13), u6!(0o17))),
        "SKZ" => Some((u5!(0o20), u6!(0o17))),
        "SZC" => Some((u5!(0o21), u6!(0o17))),
        "SZZ" => Some((u5!(0o22), u6!(0o17))),
        "SZN" => Some((u5!(0o23), u6!(0o17))),
        "SKN" => Some((u5!(0o30), u6!(0o17))),
        "SNC" => Some((u5!(0o31), u6!(0o17))),
        "SNZ" => Some((u5!(0o32), u6!(0o17))),
        "SNN" => Some((u5!(0o33), u6!(0o17))),
        "CYR" => Some((u5!(0o04), u6!(0o17))),
        "MCR" => Some((u5!(0o05), u6!(0o17))),
        "MZR" => Some((u5!(0o06), u6!(0o17))),
        "MNR" => Some((u5!(0o07), u6!(0o17))),
        "SNR" => Some((u5!(0o34), u6!(0o17))),
        "SZR" => Some((u5!(0o24), u6!(0o17))),
        "SUR" => Some((u5!(0o14), u6!(0o17))),
        "LDE" => Some((u5!(0o00), u6!(0o20))),
        "SPF" => Some((u5!(0o00), u6!(0o21))),
        "SPG" => Some((u5!(0o00), u6!(0o22))),
        "LDA" => Some((u5!(0o00), u6!(0o24))),
        "LDB" => Some((u5!(0o00), u6!(0o25))),
        "LDC" => Some((u5!(0o00), u6!(0o26))),
        "LDD" => Some((u5!(0o00), u6!(0o27))),
        "STE" => Some((u5!(0o00), u6!(0o30))),
        "FLF" => Some((u5!(0o00), u6!(0o31))),
        "FLG" => Some((u5!(0o00), u6!(0o32))),
        "STA" => Some((u5!(0o00), u6!(0o34))),
        "STB" => Some((u5!(0o00), u6!(0o35))),
        "STC" => Some((u5!(0o00), u6!(0o36))),
        "STD" => Some((u5!(0o00), u6!(0o37))),
        "ITE" => Some((u5!(0o00), u6!(0o40))),
        "ITA" => Some((u5!(0o00), u6!(0o41))),
        "UNA" => Some((u5!(0o00), u6!(0o42))),
        "SED" => Some((u5!(0o00), u6!(0o43))),
        "JOV" => Some((u5!(0o00), u6!(0o45))),
        "JPA" => Some((u5!(0o00), u6!(0o46))),
        "JNA" => Some((u5!(0o00), u6!(0o47))),
        "EXA" => Some((u5!(0o00), u6!(0o54))),
        "INS" => Some((u5!(0o00), u6!(0o55))),
        "COM" => Some((u5!(0o00), u6!(0o56))),
        "TSD" => Some((u5!(0o00), u6!(0o57))),
        "CYA" => Some((u5!(0o00), u6!(0o60))),
        "CYB" => Some((u5!(0o00), u6!(0o61))),
        "CAB" => Some((u5!(0o00), u6!(0o62))),
        "NOA" => Some((u5!(0o00), u6!(0o64))),
        "DSA" => Some((u5!(0o00), u6!(0o65))),
        "NAB" => Some((u5!(0o00), u6!(0o66))),
        "ADD" => Some((u5!(0o00), u6!(0o67))),
        "SCA" => Some((u5!(0o00), u6!(0o70))),
        "SCB" => Some((u5!(0o00), u6!(0o71))),
        "SAB" => Some((u5!(0o00), u6!(0o72))),
        "TLY" => Some((u5!(0o00), u6!(0o74))),
        "DIV" => Some((u5!(0o00), u6!(0o75))),
        "MUL" => Some((u5!(0o00), u6!(0o76))),
        "SUB" => Some((u5!(0o00), u6!(0o77))),
        _ => None,
    }
}

pub(super) fn symbol_or_literal<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, SymbolOrLiteral, ExtraWithoutContext<'a>> + Clone
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

fn opcode_to_literal(code: Unsigned6Bit, cfgbits: Unsigned5Bit, span: Span) -> LiteralValue {
    let bits = Unsigned36Bit::ZERO
        .bitor(u64::from(code).shl(24))
        .bitor(u64::from(cfgbits).shl(30))
        .bitor(helpers::opcode_auto_hold_bit(code));
    LiteralValue::from((span, Script::Normal, bits))
}

pub(super) fn opcode<'a, I>() -> impl Parser<'a, I, LiteralValue, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    symex::symex_syllable(Script::Normal)
        .filter(|mnemonic| opcode_code(mnemonic).is_some())
        .try_map_with(|mnemonic, extra| match opcode_code(mnemonic.as_str()) {
            Some((cfgbits, code)) => Ok(opcode_to_literal(code, cfgbits, extra.span())),
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
) -> impl Parser<'a, I, SymbolName, ExtraWithoutContext<'a>> + Clone
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    symex::parse_symex(rule, script_required)
}

pub(super) fn operator<'a, I>(
    script_required: Script,
) -> impl Parser<'a, I, Operator, ExtraWithoutContext<'a>> + Clone
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

fn asterisk_indirection_fragment<'srcbody, I>()
-> impl Parser<'srcbody, I, InstructionFragment, ExtraWithoutContext<'srcbody>> + Clone
where
    I: Input<'srcbody, Token = Tok, Span = Span> + ValueInput<'srcbody>,
{
    just(Tok::Asterisk(Script::Normal))
        .map_with(|_, extra| InstructionFragment::DeferredAddressing(extra.span()))
}

/// The pipe construct is described in section 6-2.8 "SPECIAL SYMBOLS"
/// of the Users Handbook.
///
/// "ADXₚ|ₜQ" should be equivalent to "ADXₚ{Qₜ}*".  So during
/// evaluation we will need to generate an RC-word containing Qₜ.
fn make_pipe_construct(
    (p, (t, maybe_spanned_q)): (
        SpannedSymbolOrLiteral,
        (SpannedSymbolOrLiteral, Option<(InstructionFragment, Span)>),
    ),
) -> InstructionFragment {
    // The variable names here are taken from the example in the
    // documentation comment.
    let tqspan = span(
        t.span.start..if let Some((_, q_span)) = maybe_spanned_q {
            q_span.end
        } else {
            t.span.end
        },
    );

    let t: CommaDelimitedFragment = CommaDelimitedFragment {
        span: t.span,
        leading_commas: None,
        holdbit: HoldBit::Unspecified,
        fragment: InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from(t.item))),
        trailing_commas: None,
    };
    let qt: UntaggedProgramInstruction = if let Some((q, q_span)) = maybe_spanned_q {
        UntaggedProgramInstruction::from(OneOrMore::with_tail(
            CommaDelimitedFragment {
                span: q_span,
                holdbit: HoldBit::Unspecified,
                leading_commas: None,
                fragment: q,
                trailing_commas: None,
            },
            vec![t],
        ))
    } else {
        UntaggedProgramInstruction::from(OneOrMore::new(t))
    };

    let rc_word_value: RegisterContaining = RegisterContaining::from(TaggedProgramInstruction {
        span: tqspan,
        tags: Vec::new(),
        instruction: qt,
    });
    InstructionFragment::PipeConstruct {
        index: p,
        rc_word_span: tqspan,
        rc_word_value,
    }
}

fn arithmetic_expression_in_any_script_allowing_spaces<'a, I>()
-> impl Parser<'a, I, (Span, Script, ArithmeticExpression), ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let g = grammar();
    choice((
        g.normal_arithmetic_expression_allowing_spaces
            .map_with(|expr, extra| (extra.span(), Script::Normal, expr)),
        g.subscript_arithmetic_expression_allowing_spaces
            .map_with(|expr, extra| (extra.span(), Script::Sub, expr)),
        g.superscript_arithmetic_expression_allowing_spaces
            .map_with(|expr, extra| (extra.span(), Script::Super, expr)),
    ))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Metacommand {
    Decimal,
    Octal,
    /// A ☛☛PUNCH meta command.
    Punch,
    DefineMacro,
    EndMacroDefinition,
}

fn named_metacommand<'a, I>(
    which: Metacommand,
) -> impl Parser<'a, I, (), ExtraWithoutContext<'a>> + use<'a, I>
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

fn metacommand<'a, 'b, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn punch<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, ExtraWithoutContext<'a>>
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

    fn base_change<'a, I>() -> impl Parser<'a, I, ManuscriptMetaCommand, ExtraWithoutContext<'a>>
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
        macros::macro_definition().map(ManuscriptMetaCommand::Macro),
    ))
    .labelled("metacommand")
}

pub(crate) fn instructions_with_comma_counts<I>(it: I) -> Vec<CommaDelimitedFragment>
where
    I: Iterator<Item = CommasOrInstruction>,
{
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
        fn null_instruction(span: Span) -> FragmentWithHold {
            FragmentWithHold {
                span,
                holdbit: HoldBit::Unspecified,
                fragment: InstructionFragment::Null(span),
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
                                unreachable!(
                                    "should be no need to interpose a null instruction between two instances of zero commas"
                                );
                            }
                        };
                        acc.push(CommasOrInstruction::I(null_instruction(null_inst_span)));
                        acc.push(CommasOrInstruction::C(maybe_commas));
                    }
                }
                CommasOrInstruction::I(inst) => {
                    acc.push(CommasOrInstruction::I(inst));
                    acc.push(CommasOrInstruction::C(None));
                }
            },
            Some(CommasOrInstruction::I(_)) => unreachable!("invariant was broken"),
            None => unreachable!("invariant was not established"),
        }
        assert!(matches!(acc.first(), Some(CommasOrInstruction::C(_))));
        assert!(matches!(acc.last(), Some(CommasOrInstruction::C(_))));
        acc
    }

    let mut it = it.peekable();

    let initial_accumulator: Vec<CommasOrInstruction> = vec![CommasOrInstruction::C({
        match it.peek() {
            None => {
                return Vec::new();
            }
            Some(CommasOrInstruction::I(_)) => None,
            Some(CommasOrInstruction::C(maybe_commas)) => {
                let c = maybe_commas.clone();
                it.next();
                c
            }
        }
    })];

    let tmp = it.fold(initial_accumulator, fold_step);
    let mut output: Vec<CommaDelimitedFragment> = Vec::with_capacity(tmp.len() / 2 + 1);
    let mut it = tmp.into_iter().peekable();
    loop {
        let maybe_before_count = it.next();
        let maybe_inst = it.next();
        match (maybe_before_count, maybe_inst) {
            (None, _) => {
                break;
            }
            (Some(CommasOrInstruction::C(before_commas)), Some(CommasOrInstruction::I(inst))) => {
                let after_commas: Option<Commas> = match it.peek() {
                    Some(CommasOrInstruction::C(commas)) => commas.clone(),
                    None => None,
                    Some(CommasOrInstruction::I(_)) => {
                        unreachable!("fold_step did not maintain its invariant")
                    }
                };
                output.push(CommaDelimitedFragment::new(
                    before_commas,
                    inst,
                    after_commas,
                ));
            }
            (Some(CommasOrInstruction::C(_)), None) => {
                // No instructions in the input.
                break;
            }
            (Some(CommasOrInstruction::I(_)), _)
            | (Some(CommasOrInstruction::C(_)), Some(CommasOrInstruction::C(_))) => {
                unreachable!("fold_step did not maintain its invariant");
            }
        }
    }
    output
}

fn tag_definition<'a, I>() -> impl Parser<'a, I, Tag, ExtraWithoutContext<'a>> + Clone
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

fn commas<'a, I>() -> impl Parser<'a, I, Commas, ExtraWithoutContext<'a>> + Clone
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

fn maybe_hold<'a, I>() -> impl Parser<'a, I, Option<HoldBit>, ExtraWithoutContext<'a>> + Clone
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

pub(crate) struct Grammar<'src, 'parser, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    assignment: Boxed<'src, 'parser, I, Equality, ExtraWithoutContext<'src>>,
    tagged_program_instruction:
        Boxed<'src, 'parser, I, TaggedProgramInstruction, ExtraWithoutContext<'src>>,
    normal_arithmetic_expression_allowing_spaces:
        Boxed<'src, 'parser, I, ArithmeticExpression, ExtraWithoutContext<'src>>,
    subscript_arithmetic_expression_allowing_spaces:
        Boxed<'src, 'parser, I, ArithmeticExpression, ExtraWithoutContext<'src>>,
    superscript_arithmetic_expression_allowing_spaces:
        Boxed<'src, 'parser, I, ArithmeticExpression, ExtraWithoutContext<'src>>,
    #[cfg(test)]
    instruction_fragment: Boxed<'src, 'parser, I, InstructionFragment, ExtraWithoutContext<'src>>,
}

fn grammar<'a: 'b, 'b, I>() -> Grammar<'a, 'b, I>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    const ALLOW_SPACES: bool = true;

    let mut comma_delimited_instructions = Recursive::declare();
    let tagged_program_instruction = (tag_definition()
        .repeated()
        .collect()
        .then(comma_delimited_instructions.clone()))
    .map_with(
        |(tags, fragments): (Vec<Tag>, OneOrMore<CommaDelimitedFragment>), extra| {
            let span: Span = extra.span();
            if let Some(t) = tags.first() {
                assert_eq!(t.span.start, span.start);
            }
            TaggedProgramInstruction {
                span,
                tags,
                instruction: UntaggedProgramInstruction::from(fragments),
            }
        },
    )
    .labelled(
        "optional tag definition followed by a (possibly comma-delimited) program instructions",
    );

    // The contents of an RC-word can contain another RC-word.  A macro
    // invocation inside an RC-word also needs the arithmetic-expression
    // parser for its arguments.  Declare this parser before the expression
    // parser and define it after both dependent parsers exist.
    let mut register_containing = Recursive::declare();
    let register_containing_for_expression = register_containing.clone();

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
                    here(script_required).map(Atom::SymbolOrLiteral),
                    named_symbol(symex_syllable_rule, script_required).map_with(
                        move |symbol_name, extra| {
                            Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(
                                script_required,
                                symbol_name,
                                extra.span(),
                            ))
                        },
                    ),
                    register_containing_for_expression.clone(),
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
        // "ADXₚ|ₜQ" should be equvialent to ADXₚ{Qₜ}*.  So we need to
        // generate an RC-word containing Qₜ.
        //
        // The Sketchpad code (file_name=102726903-05-01-acc.pdf, page
        // 16) contains a line which uses the pipe construct without a
        // value for Q: "INX ₚ|ₜ" (p is @sub_beta@ and t is
        // @sub_alpha@).  For this case we assume the value zero.
        let spanned_rc_word_fragment = symbol_or_literal(Script::Sub) // this is p
            .map_with(|p, extra| SpannedSymbolOrLiteral {
                item: p,
                span: extra.span(),
            })
            .boxed();

        let q = program_instruction_fragment
            .clone()
            .map_with(|q, extra| (q, extra.span()));
        let tq = symbol_or_literal(Script::Sub) // this is t
            .map_with(|t, extra| SpannedSymbolOrLiteral {
                item: t,
                span: extra.span(),
            })
            .then(q.or_not())
            .boxed();
        let pipe_construct = spanned_rc_word_fragment
            .then_ignore(just(Tok::Pipe(Script::Sub)))
            .then(tq)
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
        .try_map_with(|config_val, extra| {
            let span: Span = extra.span();
            let range: Range<usize> = span.into();
            let slice: &str = &extra.state().body[range];

            if slice.contains(' ') {
                // Spaces in configuration values are prohibited by
                // the rule given in the Users handbook, section 6-2.1.
                Err(Rich::custom(
                    span,
                    format!("configuration value '{slice}' should not contain spaces"),
                ))
            } else {
                Ok(InstructionFragment::Config(config_val))
            }
        })
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
                |(maybe_hold, fragment): (Option<HoldBit>, InstructionFragment), extra| {
                    let span = extra.span();
                    FragmentWithHold {
                        span,
                        holdbit: maybe_hold.unwrap_or(HoldBit::Unspecified),
                        fragment,
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
        .map(|cdfs| match OneOrMore::try_from_iter(cdfs.into_iter()) {
            Ok(cdfs) => cdfs,
            Err(_) => {
                unreachable!("instructions_with_comma_counts generated an empty output");
            }
        })
    });

    let nested_macro_arg = choice((
        arith_expr.clone()(ALLOW_SPACES, Script::Normal)
            .map_with(|expr, extra| (extra.span(), Script::Normal, expr)),
        arith_expr.clone()(ALLOW_SPACES, Script::Sub)
            .map_with(|expr, extra| (extra.span(), Script::Sub, expr)),
        arith_expr.clone()(ALLOW_SPACES, Script::Super)
            .map_with(|expr, extra| (extra.span(), Script::Super, expr)),
    ))
    .or_not()
    .map_with(|got, extra| match got {
        Some((span, script, expr)) => (span, Some((script, expr))),
        None => (extra.span(), None),
    })
    .boxed();

    let nested_macro_invocation = Ext(macros::MacroInvocationParser::new(
        nested_macro_arg,
        macros::defined_macro_name().boxed(),
    ));

    let expanded_macro = nested_macro_invocation.try_map_with(|invocation, extra| {
        let expansion = invocation.substitute_macro_parameters(extra.state().macros());
        if expansion
            .local_symbols
            .as_ref()
            .is_some_and(|symbols| !symbols.is_empty())
            || expansion
                .instructions
                .iter()
                .any(|instruction| !instruction.tags.is_empty())
        {
            return Err(Rich::custom(
                extra.span(),
                "macro expansion inside an RC-word cannot yet contain local symbols",
            ));
        }
        OneOrMore::try_from_iter(
            expansion
                .instructions
                .into_iter()
                .map(RegisterContaining::from),
        )
        .map_err(|_| Rich::custom(extra.span(), "macro expansion inside an RC-word is empty"))
    });

    // Parse {E} where E is either one instruction or a macro expansion.
    register_containing.define(
        choice((
            expanded_macro,
            tagged_program_instruction
                .clone()
                .map(|instruction| OneOrMore::new(RegisterContaining::from(instruction))),
        ))
        .delimited_by(
            just(Tok::LeftBrace(Script::Normal)),
            just(Tok::RightBrace(Script::Normal)),
        )
        .map_with(|words, extra| Atom::RcRef(extra.span(), RegistersContaining::from_words(words)))
        .labelled("RC-word")
        .boxed(),
    );

    // Assginments are called "equalities" in the TX-2 Users Handbook.
    // See section 6-2.2, "SYMEX DEFINITON - TAGS - EQUALITIES -
    // AUTOMATIC ASSIGNMENT".
    let assignment = (symex::parse_symex(SymexSyllableRule::Multiple, Script::Normal)
        .then_ignore(just(Tok::Equals(Script::Normal)))
        .then(comma_delimited_instructions.clone().map_with(
            |val: OneOrMore<CommaDelimitedFragment>, extra| {
                EqualityValue::from((extra.span(), UntaggedProgramInstruction::from(val)))
            },
        )))
    .map_with(|(name, value), extra| Equality {
        span: extra.span(),
        name,
        value,
    })
    .labelled("equality (assignment)");

    let tagged_program_instruction = tagged_program_instruction.clone();

    Grammar {
        assignment: assignment.boxed(),
        tagged_program_instruction: tagged_program_instruction.boxed(),
        normal_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Normal,
        )
        .boxed(),
        superscript_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Super,
        )
        .boxed(),
        subscript_arithmetic_expression_allowing_spaces: arith_expr.clone()(
            ALLOW_SPACES,
            Script::Sub,
        )
        .boxed(),
        #[cfg(test)]
        instruction_fragment: program_instruction_fragment.boxed(),
    }
}

#[cfg(test)]
fn tagged_instruction<'a, I>()
-> impl Parser<'a, I, TaggedProgramInstruction, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    grammar().tagged_program_instruction
}

fn manuscript_line<'a, 'b, I>(
    grammar: &Grammar<'a, 'b, I>,
) -> impl Parser<'a, I, ManuscriptLine, ExtraWithoutContext<'a>>
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

    fn parse_and_execute_metacommand<'a, I>()
    -> impl Parser<'a, I, ManuscriptLine, ExtraWithoutContext<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        metacommand()
            .map_with(|cmd, extra| {
                execute_metacommand(&mut extra.state().numeral_mode, &cmd);
                ManuscriptLine::Meta(cmd)
            })
            .labelled("metacommand")
    }

    fn build_code_line(
        (maybe_origin, statement): (Option<Origin>, TaggedProgramInstruction),
    ) -> ManuscriptLine {
        match maybe_origin {
            None => ManuscriptLine::StatementOnly(statement),
            Some(origin) => ManuscriptLine::OriginAndStatement(origin, statement),
        }
    }

    fn line<'a, 'b, I>(
        grammar: &Grammar<'a, 'b, I>,
    ) -> impl Parser<'a, I, ManuscriptLine, ExtraWithoutContext<'a>>
    where
        I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
    {
        fn origin<'a, I>() -> impl Parser<'a, I, Origin, ExtraWithoutContext<'a>>
        where
            I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
        {
            /// An address expression is a literal value or a symex.  That is I
            /// think it's not required that an arithmetic expression
            /// (e.g. "5+BAR") be accepted in an origin notation (such as
            /// "<something>|").
            fn literal_address_expression<'a, I>()
            -> impl Parser<'a, I, Origin, ExtraWithoutContext<'a>>
            where
                I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
            {
                literal(Script::Normal)
                    .then_ignore(just(Tok::Pipe(Script::Normal)))
                    .try_map(|lit, span| match Address::try_from(lit.value()) {
                        Ok(addr) => Ok(Origin::Literal(span, addr)),
                        Err(e) => Err(Rich::custom(span, format!("not a valid address: {e}"))),
                    })
                    .labelled("literal address expression")
            }

            fn symbolic_address_expression<'a, I>()
            -> impl Parser<'a, I, Origin, ExtraWithoutContext<'a>>
            where
                I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
            {
                named_symbol(SymexSyllableRule::Multiple, Script::Normal)
                    .then_ignore(just(Tok::Pipe(Script::Normal)))
                    .map_with(|name, extra| Origin::Symbolic(extra.span(), name))
                    .labelled("symbolic address expression")
            }

            // An origin specification is an expression followed by a
            // (normal-case) pipe symbol.
            choice((literal_address_expression(), symbolic_address_expression()))
                .labelled("origin specification")
        }

        let optional_origin_with_statement = origin()
            .or_not()
            .then(grammar.tagged_program_instruction.clone())
            .map(build_code_line)
            .labelled("statement with origin");

        // TODO: also allowed: "T1->T2->ORIGIN|"
        let origin_only = origin().map(ManuscriptLine::OriginOnly);
        let tags_only = tag_definition()
            .repeated()
            .at_least(1)
            .collect()
            .map(ManuscriptLine::TagsOnly);
        let equality = grammar.assignment.clone().map(ManuscriptLine::Eq);

        choice((
            // We have to parse an assignment first here, in order to
            // accept "FOO=2" as an assignment rather than the instruction
            // fragment "FOO" followed by a syntax error.
            equality,
            macros::macro_invocation().map(ManuscriptLine::Macro),
            // Ignore whitespace after the metacommand but not before it.
            parse_and_execute_metacommand(),
            optional_origin_with_statement,
            // Because we prefer to parse a statement if one exists,
            // the origin_only alternative has to appear after the
            // alternative which parses a statement.
            origin_only,
            // Similarly for lines containing only tag efinitions.
            tags_only,
        ))
    }

    line(grammar)
}

fn end_of_line<'a, I>() -> impl Parser<'a, I, (), ExtraWithoutContext<'a>>
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

fn terminated_manuscript_line<'a, 'b, I>(
    grammar: &Grammar<'a, 'b, I>,
) -> impl Parser<'a, I, Option<(Span, ManuscriptLine)>, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // If we support INSERT, DELETE, REPLACE, we will need to
    // separate the processing of the metacommands and the
    // generation of the assembled code.
    manuscript_line(grammar)
        .or_not()
        .map_with(|maybe_line, extra| maybe_line.map(|line| (extra.span(), line)))
        .then_ignore(end_of_line())
}

pub(crate) fn source_file<'a, 'b, I>(
    grammar: &Grammar<'a, 'b, I>,
) -> impl Parser<'a, I, SourceFile, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    fn inconsistency_error<'src>(
        span: Span,
        name: &SymbolName,
        what: &str,
    ) -> chumsky::error::Rich<'src, lexer::Token> {
        Rich::custom(
            span,
            format!("internal error: inconsistent parser state for macro {name}: {what}"),
        )
    }

    fn check_consistent<'a>(
        macro_def_in_source_file: Option<&MacroDefinition>,
        macro_def_in_state: Option<&MacroDefinition>,
    ) -> Result<(), chumsky::error::Rich<'a, lexer::Token>> {
        match (macro_def_in_source_file, macro_def_in_state) {
            (None, None) => {
                panic!("all_name is incorrect");
            }
            (None, Some(state_def)) => Err(inconsistency_error(
                state_def.span,
                &state_def.name,
                "missing from SourceFile output",
            )),
            (Some(source_file_def), None) => Err(inconsistency_error(
                source_file_def.span,
                &source_file_def.name,
                "missing from State",
            )),
            (Some(source_file_def), Some(state_def)) => {
                if source_file_def == state_def {
                    Ok(())
                } else {
                    Err(inconsistency_error(
                        source_file_def.span,
                        &source_file_def.name,
                        "inconsistently defined",
                    ))
                }
            }
        }
    }

    terminated_manuscript_line(grammar)
        .repeated()
        .collect()
        .try_map_with(|lines: Vec<Option<(Span, ManuscriptLine)>>, extra| {
            // Filter out empty lines.
            let lines: Vec<(Span, ManuscriptLine)> = lines.into_iter().flatten().collect();
            let state_macros: BTreeMap<SymbolName, MacroDefinition> =
                extra.state().macros().clone();

            let source_file: SourceFile = manuscript_lines_to_source_file(lines)?;

            let all_names: BTreeSet<&SymbolName> = source_file
                .macros
                .keys()
                .chain(state_macros.keys())
                .collect();
            for name in all_names {
                check_consistent(
                    source_file.macros.get(name),
                    extra.state().macros().get(name),
                )?;
            }
            Ok(source_file)
        })
}

type Mig<I, O> = chumsky::input::MappedInput<
    Tok,
    SimpleSpan,
    chumsky::input::Stream<std::vec::IntoIter<(Tok, SimpleSpan)>>,
    fn(I) -> O,
>;
pub(crate) type Mi = Mig<(Tok, SimpleSpan), (Tok, SimpleSpan)>;

fn tokenize(input: &str, span_offset: usize) -> Vec<(Tok, SimpleSpan)> {
    let scanner = lexer::Lexer::new(input).spanned();
    scanner
        .map(|(token, tokspan): (Tok, Range<usize>)| {
            let adjusted_span = (tokspan.start + span_offset)..(tokspan.end + span_offset);
            (token, adjusted_span)
        })
        .map(|item: (Tok, Range<usize>)| -> (Tok, Span) {
            match item {
                (Tok::Tab, span) => {
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
                    (Tok::Error(lexer::ErrorTokenKind::Tab), span.into())
                }
                (tok, span) => {
                    // Turn the `Range<usize>` spans logos gives us into
                    // chumsky's `SimpleSpan` via `Into`, because it's
                    // easier to work with
                    (tok, span.into())
                }
            }
        })
        .collect()
}

pub(crate) fn tokenize_and_parse_with<'a, P, T>(
    input: &'a str,
    span_offset: usize,
    state: &mut State<'a>,
    parser: P,
) -> (Option<T>, Vec<Rich<'a, Tok>>)
where
    P: Parser<'a, Mi, T, ExtraWithoutContext<'a>>,
{
    let tokens = tokenize(input, span_offset);
    let end_span: SimpleSpan = SimpleSpan::new(
        0,
        tokens.iter().map(|(_, span)| span.end).max().unwrap_or(0),
    );
    let token_stream: Mi = Stream::from_iter(tokens).map(end_span, |unchanged| unchanged);
    parser
        .parse_with_state(token_stream, state)
        .into_output_errors()
}

fn set_initial_numeral_mode(state: &mut State) {
    state.numeral_mode.set_numeral_mode(NumeralMode::Octal);
}

pub(crate) fn parse_source_file<'src>(
    source_file_body: &'src str,
) -> (Option<SourceFile>, Vec<Rich<'src, Tok>>) {
    let mut state = State::with_setup(source_file_body, set_initial_numeral_mode);
    set_initial_numeral_mode(&mut state);

    let mut errors: Vec<Rich<'src, lexer::Token>> =
        match macros::parse_unparsed_macro_definitions_only(source_file_body, &mut state) {
            Ok(errs) => errs,
            Err(errs) => {
                return (None, errs);
            }
        };

    let g = grammar();
    let parser = source_file(&g);
    let (maybe_source_file, new_errors) =
        tokenize_and_parse_with(source_file_body, 0, &mut state, parser);
    errors.extend(new_errors);
    (maybe_source_file, errors)
}

// Local Variables:
// mode: rustic
// lsp-rust-analyzer-server-display-inlay-hints: nil
// End:
