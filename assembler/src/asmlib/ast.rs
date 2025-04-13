//! Abstract syntax representation.   It's mostly not actually a tree.
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;
use std::ops::Shl;

use chumsky::span::Span as _;

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use crate::eval::{HereValue, SymbolLookupFailure, SymbolValue};
use crate::symtab::LookupOperation;

use super::eval::{Evaluate, RcBlock, SymbolContext, SymbolDefinition, SymbolLookup, SymbolUse};
use super::glyph;
use super::state::NumeralMode;
use super::symbol::{SymbolName, SymbolOrHere};
use super::symtab::SymbolTable;
use super::types::{BlockIdentifier, Span};

pub(crate) trait RcAllocator {
    fn allocate(&mut self, span: Span, value: Unsigned36Bit) -> Address;
}

/// Eventually we will support symbolic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LiteralValue {
    span: Span,
    elevation: Script,
    value: Unsigned36Bit,
}

impl LiteralValue {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value << self.elevation.shift()
    }

    pub(crate) fn unshifted_value(&self) -> Unsigned36Bit {
        self.value
    }

    #[cfg(test)]
    pub(crate) fn span(&self) -> &Span {
        &self.span
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<R: RcAllocator>(
        &self,
        _target_address: &HereValue,
        _symtab: &mut SymbolTable,
        _rc_allocator: &mut R,
        _op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(self.value())
    }
}

impl From<(Span, Script, Unsigned36Bit)> for LiteralValue {
    fn from((span, elevation, value): (Span, Script, Unsigned36Bit)) -> LiteralValue {
        LiteralValue {
            span,
            elevation,
            value,
        }
    }
}

impl std::fmt::Display for LiteralValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = self.value.to_string();
        format_elevated_chars(f, &self.elevation, &s)
    }
}

fn write_glyph_name(f: &mut Formatter<'_>, elevation: &Script, ch: char) -> fmt::Result {
    let prefix: &'static str = match elevation {
        Script::Sub => "sub_",
        Script::Super => "sup_",
        Script::Normal => "",
    };
    let name: &'static str = match glyph::name_from_glyph(ch) {
        Some(n) => n,
        None => {
            panic!("There is no glyph name for character '{ch}'");
        }
    };
    write!(f, "@{prefix}{name}@")
}

fn format_elevated_chars(f: &mut Formatter<'_>, elevation: &Script, s: &str) -> fmt::Result {
    match elevation {
        Script::Normal => {
            f.write_str(s)?;
        }
        Script::Super => {
            for ch in s.chars() {
                match superscript_char(ch) {
                    Ok(superchar) => {
                        f.write_char(superchar)?;
                    }
                    Err(_) => {
                        write_glyph_name(f, elevation, ch)?;
                    }
                }
            }
        }
        Script::Sub => {
            for ch in s.chars() {
                match subscript_char(ch) {
                    Ok(sub) => {
                        f.write_char(sub)?;
                    }
                    Err(_) => {
                        write_glyph_name(f, elevation, ch)?;
                    }
                }
            }
        }
    }
    Ok(())
}

/// The Users Handbook specifies that the operators are the four
/// arithmetic operators (+-×/) and the logical operators ∧ (AND), ∨
/// (OR), and a circled ∨ meaning XOR.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Operator {
    Add,
    LogicalAnd,
    LogicalOr, // "union" in the Users Handbook
    Multiply,
    Subtract,
    Divide,
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_char(match self {
            Operator::Add => '+',
            Operator::LogicalAnd => '∧',
            Operator::LogicalOr => '∨',
            Operator::Multiply => '\u{00D7}',
            Operator::Subtract => '-',
            Operator::Divide => '/',
        })
    }
}

/// A molecule is an arithmetic expression all in normal script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArithmeticExpression {
    first: Atom,
    tail: Vec<(Operator, Atom)>,
}

impl std::fmt::Display for ArithmeticExpression {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.first)?;
        for (op, atom) in self.tail.iter() {
            write!(f, "{op}{atom}")?;
        }
        Ok(())
    }
}

impl From<Atom> for ArithmeticExpression {
    fn from(a: Atom) -> ArithmeticExpression {
        ArithmeticExpression {
            first: a,
            tail: Vec::new(),
        }
    }
}

impl From<SymbolOrLiteral> for ArithmeticExpression {
    fn from(value: SymbolOrLiteral) -> Self {
        ArithmeticExpression::from(Atom::from(value))
    }
}

impl ArithmeticExpression {
    pub(crate) fn with_tail(first: Atom, tail: Vec<(Operator, Atom)>) -> ArithmeticExpression {
        ArithmeticExpression { first, tail }
    }

    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1 + self.tail.len());
        result.extend(self.first.symbol_uses());
        result.extend(self.tail.iter().flat_map(|(_op, x)| x.symbol_uses()));
        result.into_iter()
    }

    fn eval_binop(left: Unsigned36Bit, binop: &Operator, right: Unsigned36Bit) -> Unsigned36Bit {
        match binop {
            Operator::Add => match left.checked_add(right) {
                Some(result) => result,
                None => {
                    // TODO: checked_add doesn't currently match the
                    // operation of the TX-2 ADD instruction with
                    // respect to (for example) overflow.  See
                    // examples 4 and 5 for the ADD instruciton in the
                    // Users Handbook, for instance.
                    //
                    // We also come here for cases like 4 + -2,
                    // because (in the context of this function) -2
                    // appears to be a large unsigned number.
                    todo!("addition overflow occurred but end-around carry is not implemented")
                }
            },
            Operator::Subtract => match left.checked_sub(right) {
                Some(result) => result,
                None => {
                    todo!("subtraction overflow occurred but this is not implemented")
                }
            },
            Operator::Multiply => match left.checked_mul(right) {
                Some(result) => result,
                None => {
                    todo!("multiplication overflow occurred but this is not implemented")
                }
            },
            Operator::Divide => {
                let sleft: Signed36Bit = left.reinterpret_as_signed();
                let sright: Signed36Bit = right.reinterpret_as_signed();
                match sleft.checked_div(sright) {
                    Some(result) => result.reinterpret_as_unsigned(),
                    None => {
                        if sright.is_positive_zero() {
                            !left
                        } else if sright.is_negative_zero() {
                            left
                        } else {
                            unreachable!("division overflow occurred but RHS is not zero")
                        }
                    }
                }
            }
            Operator::LogicalAnd => left.and(right.into()),
            Operator::LogicalOr => left.bitor(right.into()),
        }
    }
}

fn fold_step<R: RcAllocator>(
    acc: Unsigned36Bit,
    (binop, right): &(Operator, Atom),
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let right: Unsigned36Bit = right.evaluate(target_address, symtab, rc_allocator, op)?;
    Ok(ArithmeticExpression::eval_binop(acc, binop, right))
}

impl Evaluate for ArithmeticExpression {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        let first: Unsigned36Bit = self
            .first
            .evaluate(target_address, symtab, rc_allocator, op)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> =
            self.tail.iter().try_fold(first, |acc, curr| {
                fold_step(acc, curr, target_address, symtab, rc_allocator, op)
            });
        result
    }
}

/// A configuration syllable can be specified by putting it in a
/// superscript, or by putting it in normal script after a ‖ symbol
/// (‖x or ‖2, for example).  This is described in section 6-2.1 of
/// the Users Handbook.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ConfigValue {
    Literal(Span, Unsigned36Bit),
    Symbol(Span, SymbolOrHere),
}

impl ConfigValue {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        match self {
            ConfigValue::Literal(_span, _value) => None,
            ConfigValue::Symbol(_span, SymbolOrHere::Here) => None,
            ConfigValue::Symbol(span, SymbolOrHere::Named(name)) => Some((
                name.to_owned(),
                *span,
                SymbolUse::Reference(SymbolContext::configuration()),
            )),
        }
        .into_iter()
    }
}

impl Evaluate for ConfigValue {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            ConfigValue::Literal(_span, value) => Ok(*value),
            ConfigValue::Symbol(span, SymbolOrHere::Here) => {
                Ok(Unsigned36Bit::from(target_address.get_address(span)?))
            }
            ConfigValue::Symbol(span, SymbolOrHere::Named(name)) => {
                let context = SymbolContext::configuration();
                match symtab.lookup_with_op(name, *span, target_address, rc_allocator, &context, op)
                {
                    Ok(SymbolValue::Final(value)) => Ok(value),
                    Err(e) => Err(e),
                }
            }
        }
        .map(|value| value.shl(30u32))
    }
}

/// Eventually we will support real expressions, but for now we only
/// suport literals and references to symbols ("equalities" in the
/// User Handbook).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Atom {
    Literal(LiteralValue),
    Symbol(Span, Script, SymbolOrHere),
    Parens(Script, Box<ArithmeticExpression>),
    RcRef(Span, Vec<InstructionFragment>),
}

impl From<SymbolOrLiteral> for Atom {
    fn from(value: SymbolOrLiteral) -> Self {
        match value {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => {
                Atom::Symbol(span, script, SymbolOrHere::Named(symbol_name))
            }
            SymbolOrLiteral::Literal(literal_value) => Atom::Literal(literal_value),
        }
    }
}

impl Atom {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Atom::Literal(_) | Atom::RcRef(_, _) | Atom::Symbol(_, _, SymbolOrHere::Here) => (),
            Atom::Symbol(span, script, SymbolOrHere::Named(name)) => {
                result.push((
                    name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                ));
            }
            Atom::Parens(_script, expr) => {
                result.extend(expr.symbol_uses());
            }
        }
        result.into_iter()
    }
}

fn symbol_name_lookup<R: RcAllocator>(
    name: &SymbolName,
    elevation: Script,
    span: Span,
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    let context = SymbolContext::from((elevation, span));
    match symtab.lookup_with_op(name, span, target_address, rc_allocator, &context, op) {
        Ok(SymbolValue::Final(value)) => Ok(value),
        Err(e) => Err(e),
    }
    .map(|value| value.shl(elevation.shift()))
}

impl Evaluate for Atom {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::Symbol(span, elevation, SymbolOrHere::Here) => {
                let value: Unsigned36Bit = target_address.get_address(span)?.into();
                Ok(value.shl(elevation.shift()))
            }
            Atom::Literal(literal) => Ok(literal.value()),
            Atom::Symbol(span, elevation, SymbolOrHere::Named(name)) => symbol_name_lookup(
                name,
                *elevation,
                *span,
                target_address,
                symtab,
                rc_allocator,
                op,
            ),
            Atom::Parens(_script, expr) => expr.evaluate(target_address, symtab, rc_allocator, op),
            Atom::RcRef(span, fragments) => {
                let value: Unsigned36Bit = evaluate_instruction_fragments(
                    fragments,
                    target_address,
                    symtab,
                    rc_allocator,
                    op,
                )?;
                let addr: Address = rc_allocator.allocate(*span, value);
                Ok(addr.into())
            }
        }
    }
}

impl From<LiteralValue> for Atom {
    fn from(literal: LiteralValue) -> Atom {
        Atom::Literal(literal)
    }
}

impl From<(Span, Script, Unsigned36Bit)> for Atom {
    fn from((span, script, v): (Span, Script, Unsigned36Bit)) -> Atom {
        Atom::from(LiteralValue::from((span, script, v)))
    }
}

fn elevated_string<'a>(s: &'a str, elevation: &Script) -> Cow<'a, str> {
    match elevation {
        Script::Normal => Cow::Borrowed(s),
        Script::Super => Cow::Owned(
            s.chars()
                .map(|ch| superscript_char(ch).unwrap_or(ch))
                .collect(),
        ),
        Script::Sub => Cow::Owned(
            s.chars()
                .map(|ch| subscript_char(ch).unwrap_or(ch))
                .collect(),
        ),
    }
}

impl std::fmt::Display for Atom {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Atom::Symbol(_span, elevation, SymbolOrHere::Here) => match elevation {
                Script::Super => f.write_str("@super_hash@"),
                Script::Normal => f.write_char('#'),
                Script::Sub => f.write_str("@sub_hash@"),
            },
            Atom::Literal(value) => value.fmt(f),
            Atom::Symbol(_span, elevation, SymbolOrHere::Named(name)) => {
                elevated_string(&name.to_string(), elevation).fmt(f)
            }
            Atom::Parens(script, expr) => elevated_string(&expr.to_string(), script).fmt(f),
            Atom::RcRef(_span, _rc_reference) => {
                // The RcRef doesn't itself record the content of the
                // {...} because that goes into the rc-block itself.
                write!(f, "{{...}}")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymbolOrLiteral {
    Symbol(Script, SymbolName, Span),
    Literal(LiteralValue),
}

impl SymbolOrLiteral {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::with_capacity(1);
        match self {
            SymbolOrLiteral::Literal(_) => (),
            SymbolOrLiteral::Symbol(script, name, span) => {
                let context: SymbolContext = (script, *span).into();
                let sym_use: SymbolUse = SymbolUse::Reference(context);
                result.push((name.clone(), *span, sym_use));
            }
        }
        result.into_iter()
    }
}

impl Evaluate for SymbolOrLiteral {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            SymbolOrLiteral::Symbol(script, symbol_name, span) => symbol_name_lookup(
                symbol_name,
                *script,
                *span,
                target_address,
                symtab,
                rc_allocator,
                op,
            ),
            SymbolOrLiteral::Literal(literal_value) => {
                literal_value.evaluate(target_address, symtab, rc_allocator, op)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InstructionFragment {
    /// Arithmetic expressions are permitted in normal case according
    /// to the Users Handbook, but currently this implementation
    /// allows them in subscript/superscript too.
    Arithmetic(ArithmeticExpression),
    /// Deferred addressing is normally specified as '*' but
    /// PipeConstruct is a different way to indicate deferred
    /// addressing.
    DeferredAddressing,
    /// A configuration syllable (specified either in superscript or with a ‖).
    Config(ConfigValue),
    /// Described in section 6-2.8 "SPECIAL SYMBOLS" of the Users Handbook.
    PipeConstruct {
        index: SymbolOrLiteral,
        rc_word_span: Span,
        rc_word_fragments: Vec<InstructionFragment>,
    },
    // TODO: subscript/superscript atom (if the `Arithmetic` variant
    // disallows subscript/superscript).
}

impl InstructionFragment {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<_> = Vec::new();
        match self {
            InstructionFragment::Arithmetic(expr) => {
                result.extend(expr.symbol_uses());
            }
            InstructionFragment::DeferredAddressing => (),
            InstructionFragment::Config(value) => {
                result.extend(value.symbol_uses());
            }
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span: _,
                rc_word_fragments,
            } => {
                result.extend(index.symbol_uses().map(|(name, span, mut symbol_use)| {
                    if let SymbolUse::Reference(context) = &mut symbol_use {
                        assert!(!context.is_address());
                        context.also_set_index();
                    };
                    (name, span, symbol_use)
                }));
                result.extend(rc_word_fragments.iter().flat_map(|frag| frag.symbol_uses()));
            }
        }
        result.into_iter()
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn index_value_of(unshifted: Unsigned36Bit) -> Unsigned36Bit {
            unshifted.shl(Script::Sub.shift())
        }

        match self {
            InstructionFragment::Arithmetic(expr) => {
                expr.evaluate(target_address, symtab, rc_allocator, op)
            }
            InstructionFragment::DeferredAddressing => Ok(DEFER_BIT),
            InstructionFragment::Config(value) => {
                value.evaluate(target_address, symtab, rc_allocator, op)
            }
            InstructionFragment::PipeConstruct {
                index: p,
                rc_word_span,
                rc_word_fragments,
            } => {
                // The pipe construct is described in section 6-2.8
                // "SPECIAL SYMBOLS" of the Users Handbook.
                //
                //
                // "ADXₚ|ₜQ" should be equivalent to "ADXₚ{Qₜ}*".
                // (Note that in the real pipe construct the "|" is
                // itself in subscript).  During parsing, the values
                // of Q and ₜ were combined into rc_word_fragments.
                // We evaluate Qₜ as rc_word_value.
                let rc_word_value: Unsigned36Bit = evaluate_instruction_fragments(
                    rc_word_fragments,
                    target_address,
                    symtab,
                    rc_allocator,
                    op,
                )?;
                let p_value: Unsigned36Bit =
                    index_value_of(p.evaluate(target_address, symtab, rc_allocator, op)?);
                let addr: Address = rc_allocator.allocate(*rc_word_span, rc_word_value);
                Ok(combine_fragment_values(
                    combine_fragment_values(Unsigned36Bit::from(addr), p_value),
                    DEFER_BIT,
                ))
            }
        }
    }
}

impl From<(Span, Script, Unsigned36Bit)> for InstructionFragment {
    fn from((span, script, v): (Span, Script, Unsigned36Bit)) -> InstructionFragment {
        // TODO: use the atomic variant instead.
        InstructionFragment::Arithmetic(ArithmeticExpression::from(Atom::from((span, script, v))))
    }
}

impl From<ArithmeticExpression> for InstructionFragment {
    fn from(expr: ArithmeticExpression) -> Self {
        InstructionFragment::Arithmetic(expr)
    }
}

// Once we support symbolic origins we should update
// ManuscriptBlock::global_symbol_definitions() to expose them.
#[derive(Debug, Clone)]
pub(crate) enum Origin {
    Literal(Span, Address),
    Symbolic(Span, SymbolName),
}

impl Ord for Origin {
    fn cmp(&self, other: &Origin) -> Ordering {
        match (self, other) {
            (Origin::Literal(_, selfaddr), Origin::Literal(_, otheraddr)) => {
                selfaddr.cmp(otheraddr)
            }
            (Origin::Symbolic(_, selfsym), Origin::Symbolic(_, othersym)) => selfsym.cmp(othersym),
            (Origin::Literal(_, _), Origin::Symbolic(_, _)) => Ordering::Less,
            (Origin::Symbolic(_, _), Origin::Literal(_, _)) => Ordering::Greater,
        }
    }
}

impl Eq for Origin {}

impl PartialEq for Origin {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl PartialOrd for Origin {
    fn partial_cmp(&self, other: &Origin) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Hash for Origin {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Origin::Literal(_, addr) => addr.hash(state),
            Origin::Symbolic(_, name) => name.hash(state),
        }
    }
}

impl Display for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Origin::Literal(_span, addr) => fmt::Display::fmt(&addr, f),
            Origin::Symbolic(_span, sym) => fmt::Display::fmt(&sym, f),
        }
    }
}

impl Origin {
    pub(crate) fn default_address() -> Address {
        // Section 6-2.5 of the User Manual states that if the
        // manuscript contains no origin specification (no vertical
        // bar) the whole program is located (correctly) at 200_000
        // octal.
        Address::new(u18!(0o200_000))
    }

    pub(crate) fn span(&self) -> &Span {
        match self {
            Origin::Literal(span, _) | Origin::Symbolic(span, _) => span,
        }
    }
}

impl Octal for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Literal(_span, address) => fmt::Octal::fmt(&address, f),
            Origin::Symbolic(_span, name) => fmt::Display::fmt(&name, f),
        }
    }
}

impl Origin {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Origin::Literal(_span, _) => (),
            Origin::Symbolic(span, name) => result.push((
                name.clone(),
                *span,
                SymbolUse::Origin(name.clone(), block_id),
            )),
        }
        result.into_iter()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum HoldBit {
    Unspecified,
    Hold,
    NotHold,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Commas {
    span: Span,
    count: usize,
}

impl Commas {
    fn implicit(&self) -> bool {
        self.count == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CommasOrInstruction {
    I(UntaggedProgramInstruction),
    C(Commas),
}

fn instructions_with_comma_counts<I>(it: I) -> Vec<(Commas, UntaggedProgramInstruction, Commas)>
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
                parts: vec![InstructionFragment::from(ArithmeticExpression::from(
                    Atom::Literal(LiteralValue {
                        span,
                        elevation: Script::Normal,
                        value: Unsigned36Bit::ZERO,
                    }),
                ))],
            }
        }

        match acc.last_mut() {
            Some(CommasOrInstruction::C(tail_comma)) => match item {
                C(item_commas) => {
                    if tail_comma.implicit() {
                        *tail_comma = item_commas;
                    } else {
                        acc.push(CommasOrInstruction::I(null_instruction(item_commas.span)));
                        acc.push(CommasOrInstruction::C(item_commas));
                    }
                }
                CommasOrInstruction::I(inst) => {
                    let span: Span = inst.span;
                    acc.push(CommasOrInstruction::I(inst));
                    acc.push(CommasOrInstruction::C(Commas { span, count: 0 }));
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
            Some(I(inst)) => Commas {
                span: inst.span,
                count: 0,
            },
            Some(C(commas)) => {
                let c = commas.clone();
                it.next();
                c
            }
        }
    })];
    dbg!(&initial_accumulator);
    let tmp = it.fold(initial_accumulator, fold_step);
    let mut output: Vec<(Commas, UntaggedProgramInstruction, Commas)> =
        Vec::with_capacity(tmp.len() / 2 + 1);
    let mut it = tmp.into_iter().peekable();
    loop {
        let maybe_before_count = it.next();
        let maybe_inst = it.next();
        match (maybe_before_count, maybe_inst) {
            (None, _) => {
                break;
            }
            (Some(C(before_commas)), Some(I(inst))) => {
                let after_commas: Commas = match it.peek() {
                    Some(CommasOrInstruction::C(commas)) => commas.clone(),
                    None => Commas {
                        span: before_commas.span,
                        count: 0,
                    },
                    Some(CommasOrInstruction::I(_)) => {
                        unreachable!("fold_step did not maintain its invariant")
                    }
                };
                output.push((before_commas, inst, after_commas));
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

#[cfg(test)]
mod comma_tests {
    use super::super::types::Span;
    use super::instructions_with_comma_counts as parent_instructions_with_comma_counts;
    use super::Commas;
    use super::CommasOrInstruction;
    use super::UntaggedProgramInstruction;
    use std::fmt::Formatter;
    use std::ops::Range;

    #[derive(Clone, Eq)]
    struct Briefly(Commas, UntaggedProgramInstruction, Commas);

    impl From<(Commas, UntaggedProgramInstruction, Commas)> for Briefly {
        fn from(value: (Commas, UntaggedProgramInstruction, Commas)) -> Self {
            Self(value.0, value.1, value.2)
        }
    }

    fn briefly(v: Vec<(Commas, UntaggedProgramInstruction, Commas)>) -> Vec<Briefly> {
        v.into_iter().map(Briefly::from).collect()
    }

    impl PartialEq<(Commas, UntaggedProgramInstruction, Commas)> for Briefly {
        fn eq(&self, other: &(Commas, UntaggedProgramInstruction, Commas)) -> bool {
            self.0 == other.0 && self.1 == other.1 && self.2 == other.2
        }
    }

    impl PartialEq<Briefly> for Briefly {
        fn eq(&self, other: &Briefly) -> bool {
            self.0 == other.0 && self.1 == other.1 && self.2 == other.2
        }
    }

    fn instructions_with_comma_counts(input: Vec<CommasOrInstruction>) -> Vec<Briefly> {
        dbg!(&input);
        let output = parent_instructions_with_comma_counts(input.into_iter());
        output
            .into_iter()
            .map(|(lc, inst, rc)| Briefly(lc, inst, rc))
            .collect()
    }

    impl std::fmt::Debug for Briefly {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            use super::*;
            let instr_string: String = match self.1.parts.as_slice() {
                [] => unreachable!(),
                [only] => match only {
                    InstructionFragment::Arithmetic(ArithmeticExpression { first, tail }) => {
                        if tail.is_empty() {
                            match first {
                                Atom::Literal(LiteralValue {
                                    span: _,
                                    elevation: Script::Normal,
                                    value,
                                }) => {
                                    format!("{value}")
                                }
                                _ => unreachable!(),
                            }
                        } else {
                            unreachable!();
                        }
                    }
                    _ => unreachable!(),
                },
                _too_many => unreachable!(),
            };
            write!(
                f,
                "({:?},UntaggedProgramInstruction({instr_string}),{:?})",
                self.0, self.2
            )
        }
    }

    fn span(range: Range<usize>) -> Span {
        Span::from(range)
    }

    fn inst(n: u16) -> UntaggedProgramInstruction {
        use super::*;
        UntaggedProgramInstruction {
            span: span(0..1),
            holdbit: HoldBit::Unspecified,
            parts: vec![InstructionFragment::from(ArithmeticExpression::from(
                Atom::Literal(LiteralValue {
                    span: span(0..1),
                    elevation: Script::Normal,
                    value: n.into(),
                }),
            ))],
        }
    }

    fn commas(count: usize) -> Commas {
        Commas {
            span: span(0..1),
            count,
        }
    }

    #[test]
    fn test_instructions_with_comma_counts_len_0_all_cases() {
        assert_eq!(instructions_with_comma_counts(Vec::new()), briefly(vec![]))
    }

    #[test]
    fn test_instructions_with_comma_counts_len_1_all_cases() {
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::I(inst(1))]),
            briefly(vec![(commas(0), inst(1), commas(0)),])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::C(commas(1))]),
            briefly(vec![]),
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_0_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(commas(1)),
                CommasOrInstruction::C(commas(2))
            ]),
            briefly(vec![(commas(1), inst(0), commas(2))])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_a() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::I(inst(1)),
                CommasOrInstruction::C(commas(1)),
            ]),
            briefly(vec![(commas(0), inst(1), commas(1))])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_b() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(commas(2)),
                CommasOrInstruction::I(inst(3)),
            ]),
            briefly(vec![(commas(2), inst(3), commas(0))])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_2_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), I(inst(2))]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(0)),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_0_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(1)), C(commas(2)), C(commas(3))]),
            briefly(vec![
                (commas(1), inst(0), commas(2)),
                (commas(2), inst(0), commas(3)),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_1_instructions() {
        use CommasOrInstruction::*;
        // CCI cases
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(1)), C(commas(2)), I(inst(3))]),
            briefly(vec![
                (commas(1), inst(0), commas(2)),
                (commas(2), inst(3), commas(0)),
            ])
        );

        // CIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(0)), I(inst(2)), C(commas(0))]),
            briefly(vec![(commas(0), inst(2), commas(0))])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(1)), I(inst(2)), C(commas(3))]),
            briefly(vec![(commas(1), inst(2), commas(3))])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(0)), I(inst(2)), C(commas(3))]),
            briefly(vec![(commas(0), inst(2), commas(3))])
        );

        // ICC cases
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), C(commas(1)), C(commas(2))]),
            briefly(vec![
                (commas(0), inst(1), commas(1)),
                (commas(1), inst(0), commas(2))
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), C(commas(2)), C(commas(3))]),
            briefly(vec![
                (commas(0), inst(1), commas(2)),
                (commas(2), inst(0), commas(3)),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_2_instructions() {
        use CommasOrInstruction::*;
        // IIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), I(inst(2)), C(commas(2))]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(2))
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), I(inst(2)), C(commas(0))]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(0))
            ])
        );

        // ICI cases
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), C(commas(2)), I(inst(2)),]),
            briefly(vec![
                (commas(0), inst(1), commas(2)),
                (commas(2), inst(2), commas(0))
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), C(commas(3)), I(inst(2)),]),
            briefly(vec![
                (commas(0), inst(1), commas(3)),
                (commas(3), inst(2), commas(0))
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), C(commas(0)), I(inst(2)),]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(0))
            ])
        );

        // CII cases
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(2)), I(inst(1)), I(inst(2)),]),
            briefly(vec![
                (commas(2), inst(1), commas(0)),
                (commas(0), inst(2), commas(0))
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![C(commas(0)), I(inst(1)), I(inst(2)),]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(0))
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_3_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(1)), I(inst(2)), I(inst(3)),]),
            briefly(vec![
                (commas(0), inst(1), commas(0)),
                (commas(0), inst(2), commas(0)),
                (commas(0), inst(3), commas(0)),
            ])
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UntaggedProgramInstruction {
    pub(crate) span: Span,
    pub(crate) holdbit: HoldBit,
    pub(crate) parts: Vec<InstructionFragment>,
}

impl UntaggedProgramInstruction {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.parts.iter().flat_map(InstructionFragment::symbol_uses)
    }
}

/// The Users Handbook implies that instruction fragments are added
/// together, and I am not sure whether they mean this literally (as
/// in, addition) or figuratively (as in a logica-or operation).  This
/// function exists to be a single place to encode this assumption.
fn combine_fragment_values(left: Unsigned36Bit, right: Unsigned36Bit) -> Unsigned36Bit {
    left | right
}

fn evaluate_instruction_fragments<R: RcAllocator>(
    parts: &[InstructionFragment],
    target_address: &HereValue,
    symtab: &mut SymbolTable,
    rc_allocator: &mut R,
    op: &mut LookupOperation,
) -> Result<Unsigned36Bit, SymbolLookupFailure> {
    fn or_looked_up_value<R: RcAllocator>(
        accumulator: Unsigned36Bit,
        frag: &InstructionFragment,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        Ok(combine_fragment_values(
            accumulator,
            frag.evaluate(target_address, symtab, rc_allocator, op)?,
        ))
    }

    parts.iter().try_fold(Unsigned36Bit::ZERO, |acc, curr| {
        or_looked_up_value(acc, curr, target_address, symtab, rc_allocator, op)
    })
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        evaluate_instruction_fragments(
            self.parts.as_slice(),
            target_address,
            symtab,
            rc_allocator,
            op,
        )
        .map(|word| match self.holdbit {
            HoldBit::Hold => word | HELD_MASK,
            HoldBit::NotHold => word & !HELD_MASK,
            HoldBit::Unspecified => word,
        })
    }
}

/// A "Tag" is a symex used as a name for a place in a program.  A tag
/// is always terminated by an arrow ("->") and [in the symbol table]
/// it set to the numerical location of the word that it tags. [from
/// section 6-2.2 of the User's Handbook].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Tag {
    pub(crate) name: SymbolName,
    pub(crate) span: Span,
}

impl Tag {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        [(
            self.name.clone(),
            self.span,
            SymbolUse::Definition(SymbolDefinition::Tag {
                block_id,
                block_offset,
                span: self.span,
            }),
        )]
        .into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TaggedProgramInstruction {
    pub(crate) tag: Option<Tag>,
    pub(crate) instruction: UntaggedProgramInstruction,
}

impl TaggedProgramInstruction {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::new();
        if let Some(tag) = self.tag() {
            result.extend(tag.symbol_uses(block_id, offset));
        }
        result.extend(self.instruction.symbol_uses());
        result.into_iter()
    }

    pub(crate) fn span(&self) -> Span {
        let begin = match self.tag() {
            Some(t) => t.span.start,
            None => self.instruction.span.start,
        };
        Span::from(begin..(self.instruction.span.end))
    }

    pub(crate) fn tag(&self) -> Option<&Tag> {
        self.tag.as_ref()
    }

    pub(crate) fn single(
        tag: Option<Tag>,
        instruction: UntaggedProgramInstruction,
    ) -> TaggedProgramInstruction {
        Self { tag, instruction }
    }
}

impl Evaluate for TaggedProgramInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction
            .evaluate(target_address, symtab, rc_allocator, op)
    }
}

const HELD_MASK: Unsigned36Bit = u36!(1 << 35);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    pub(crate) blocks: BTreeMap<BlockIdentifier, ManuscriptBlock>,
    pub(crate) macros: Vec<MacroDefinition>,
}

impl SourceFile {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.blocks
            .iter()
            .flat_map(|(block_id, block)| block.symbol_uses(*block_id))
    }

    pub(crate) fn global_symbol_references(
        &self,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolContext)> + '_ {
        self.symbol_uses()
            .filter_map(|(name, span, sym_use)| match sym_use {
                SymbolUse::Reference(context) => Some((name, span, context)),
                SymbolUse::Definition(_) => None,
                // An origin specification is either a reference or a definition, depending on how it is used.
                SymbolUse::Origin(name, block) => {
                    Some((name, span, SymbolContext::origin(block, span)))
                }
            })
    }

    pub(crate) fn global_symbol_definitions(
        &self,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolDefinition)> + '_ {
        self.symbol_uses()
            .filter_map(|(name, span, sym_use)| match sym_use {
                SymbolUse::Reference(_context) => None,
                SymbolUse::Definition(def) => Some((name, span, def)),
                // An origin specification is either a reference or a definition, depending on how it is used.
                SymbolUse::Origin(name, block) => Some((
                    name,
                    span,
                    SymbolDefinition::Undefined(SymbolContext::origin(block, span)),
                )),
            })
    }
}

/// Represents the ☛☛PUNCH metacommand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PunchCommand(pub(crate) Option<Address>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptMetaCommand {
    // TODO: implement the T= metacommand.
    // TODO: implement the RC metacommand.
    // TODO: implement the XXX metacommand.
    BaseChange(NumeralMode),
    Punch(PunchCommand),
    Macro(MacroDefinition),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptLine {
    MetaCommand(ManuscriptMetaCommand), // can actually span several lines.
    JustOrigin(Origin),
    Code(Option<Origin>, Statement),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Statement {
    // The RHS of an assignment can be "any 36-bit value" (see TX-2
    // Users Handbook, section 6-2.2, page 156 = 6-6).  Hence if the
    // RHS of the assignment is symbolic the user needs to be able to
    // set the hold bit with "h".  However, since we don't allow tags
    // on the RHS, the value cannot be a TaggedProgramInstruction.
    Assignment(Span, SymbolName, UntaggedProgramInstruction), // User Guide calls these "equalities".
    Instruction(TaggedProgramInstruction),
}

impl Statement {
    fn span(&self) -> Span {
        match self {
            Statement::Assignment(span, _, _) => *span,
            Statement::Instruction(inst) => inst.span(),
        }
    }

    fn emitted_instruction_count(&self) -> Unsigned18Bit {
        match self {
            Statement::Assignment(_, _, _) => Unsigned18Bit::ZERO,
            Statement::Instruction(_) => Unsigned18Bit::ONE,
        }
    }

    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        match self {
            Statement::Assignment(span, symbol, expression) => {
                vec![(
                    symbol.clone(),
                    *span,
                    SymbolUse::Definition(
                        // TODO: the expression.clone() on the next line is expensive.
                        SymbolDefinition::Equality(expression.clone()),
                    ),
                )]
            }
            Statement::Instruction(inst) => inst.symbol_uses(block_id, offset).collect(),
        }
        .into_iter()
    }
}

impl From<(Span, Unsigned36Bit)> for Statement {
    fn from((span, value): (Span, Unsigned36Bit)) -> Statement {
        Statement::Instruction(TaggedProgramInstruction::single(
            None,
            UntaggedProgramInstruction {
                span,
                holdbit: HoldBit::Unspecified,
                parts: vec![InstructionFragment::from(ArithmeticExpression::from(
                    Atom::Literal(LiteralValue {
                        span,
                        elevation: Script::Normal,
                        value,
                    }),
                ))],
            },
        ))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroArgument {
    pub(crate) name: SymbolName,
    pub(crate) span: Span,
    pub(crate) preceding_terminator: char,
}

/// As defined with ☛☛DEF, a macro's name is followed by a terminator,
/// or by a terminator and some arguments.  We model each argument as
/// being introduced by its preceding terminator.  If there are no
/// arguments, MacroArguments::Zero(ch) represents that uses of the
/// macro's name are followed by the indicated terminator character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MacroArguments {
    Zero(char),
    OneOrMore(Vec<MacroArgument>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroDefinition {
    pub(crate) name: SymbolName, // composite character macros are not yet supported
    pub(crate) args: MacroArguments,
    // body should probably be a sequence of ManuscriptLine in order
    // to allow an origin specification to exist within a macro body.
    // But that is not supported yet.
    pub(crate) body: Vec<Statement>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ManuscriptBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) statements: Vec<Statement>,
}

impl ManuscriptBlock {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::new();
        if let Some(origin) = self.origin.as_ref() {
            result.extend(origin.symbol_uses(block_id));
        }
        for (offset, statement) in self.statements.iter().enumerate() {
            let off: Unsigned18Bit = Unsigned18Bit::try_from(offset)
                .expect("block should not be larger than the TX-2's memory");
            result.extend(statement.symbol_uses(block_id, off));
        }
        result.into_iter()
    }

    pub(crate) fn instruction_count(&self) -> Unsigned18Bit {
        self.statements
            .iter()
            .map(|st| st.emitted_instruction_count())
            .sum()
    }

    pub(crate) fn origin_span(&self) -> Span {
        if let Some(origin) = self.origin.as_ref() {
            *origin.span()
        } else if let Some(first) = self.statements.first() {
            first.span()
        } else {
            Span::from(0..0)
        }
    }
}

#[derive(Debug)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
    pub(crate) entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn new(
        blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
        entry_point: Option<Address>,
    ) -> Self {
        Self {
            blocks,
            entry_point,
        }
    }

    pub(crate) fn take_rc_block(&mut self) -> RcBlock {
        let max_occupied_addr: Option<Address> =
            self.blocks.values().map(LocatedBlock::following_addr).max();
        RcBlock {
            address: max_occupied_addr.unwrap_or_else(Origin::default_address),
            words: Vec::new(),
        }
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) origin: Option<Origin>,
    pub(crate) location: Option<Address>,
    pub(crate) statements: Vec<Statement>,
}

impl Block {
    pub(crate) fn emitted_instruction_count(&self) -> Unsigned18Bit {
        self.statements
            .iter()
            .map(|stmt| stmt.emitted_instruction_count())
            .sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedBlock {
    pub(crate) location: Address,
    pub(crate) statements: Vec<Statement>,
}

impl LocatedBlock {
    pub(crate) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.statements
            .iter()
            .map(|stmt| stmt.emitted_instruction_count())
            .sum()
    }

    pub(crate) fn following_addr(&self) -> Address {
        self.location.index_by(self.emitted_word_count())
    }
}
