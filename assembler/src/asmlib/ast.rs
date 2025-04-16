//! Abstract syntax representation.   It's mostly not actually a tree.
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;
use std::ops::{Shl, Shr};

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use crate::eval::{combine_fragment_values, HereValue, SymbolLookupFailure, SymbolValue};
use crate::symtab::LookupOperation;

use super::eval::{
    evaluate_tagged_program_instructions, Evaluate, RcBlock, SymbolContext, SymbolDefinition,
    SymbolLookup, SymbolUse,
};
use super::glyph;
use super::span::*;
use super::state::NumeralMode;
use super::symbol::{SymbolName, SymbolOrHere};
use super::symtab::SymbolTable;
use super::types::*;

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

    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1 + self.tail.len());
        result.extend(self.first.symbol_uses(block_id, block_offset));
        result.extend(
            self.tail
                .iter()
                .flat_map(|(_op, x)| x.symbol_uses(block_id, block_offset)),
        );
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
    RcRef(Span, Vec<TaggedProgramInstruction>),
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
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Atom::Literal(_) | Atom::Symbol(_, _, SymbolOrHere::Here) => (),
            Atom::Symbol(span, script, SymbolOrHere::Named(name)) => {
                result.push((
                    name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                ));
            }
            Atom::Parens(_script, expr) => {
                result.extend(expr.symbol_uses(block_id, block_offset));
            }
            Atom::RcRef(_span, tagged_instructions) => {
                // Tags defined inside the RC-word are not counted as
                // defined outside it.  But if we refer to a symbol
                // inside the RC-word it counts as a reference for the
                // purpose of determining which contexts it has been
                // used in.
                for symbol_use in tagged_instructions
                    .iter()
                    .flat_map(|instr| instr.symbol_uses(block_id, block_offset))
                {
                    match &symbol_use {
                        (_, _, SymbolUse::Reference(_)) => {
                            result.push(symbol_use);
                        }
                        (name, _span, SymbolUse::Definition(SymbolDefinition::Tag { .. })) => {
                            panic!("Found definition of tag {name} inside an RC-word; this is allowed but is not yet supported.");
                        }
                        (name, _span, SymbolUse::Origin(_name, _block)) => {
                            unreachable!("Found origin {name} inside an RC-word; the parser should have rejected this.");
                        }
                        (name, span, SymbolUse::Definition(_)) => {
                            // e.g. we have an input like
                            //
                            // { X = 2 }
                            //
                            //
                            // Ideally we would issue an error for
                            // this, but since this function cannot
                            // fail, it's better to do that at the
                            // time we parse the RC-word reference
                            // (thus eliminating this case).
                            //
                            // When working on this case we should
                            // figure out if an equality is allowed
                            // inside a macro expansion.
                            panic!("Found unexpected definition of {name} inside RC-word reference at {span:?}");
                        }
                    }
                }
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
            Atom::RcRef(span, tagged_program_instructions) => {
                let value: Unsigned36Bit = evaluate_tagged_program_instructions(
                    tagged_program_instructions,
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
        rc_word_value: Box<(InstructionFragment, Atom)>,
    },
    // TODO: subscript/superscript atom (if the `Arithmetic` variant
    // disallows subscript/superscript).
}

impl InstructionFragment {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<_> = Vec::new();
        match self {
            InstructionFragment::Arithmetic(expr) => {
                result.extend(expr.symbol_uses(block_id, block_offset));
            }
            InstructionFragment::DeferredAddressing => (),
            InstructionFragment::Config(value) => {
                result.extend(value.symbol_uses());
            }
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span: _,
                rc_word_value,
            } => {
                result.extend(index.symbol_uses().map(|(name, span, mut symbol_use)| {
                    if let SymbolUse::Reference(context) = &mut symbol_use {
                        assert!(!context.is_address());
                        context.also_set_index();
                    };
                    (name, span, symbol_use)
                }));
                let (base, index) = rc_word_value.as_ref();
                result.extend(base.symbol_uses(block_id, block_offset));
                result.extend(index.symbol_uses(block_id, block_offset));
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
                rc_word_value,
            } => {
                // The pipe construct is described in section 6-2.8
                // "SPECIAL SYMBOLS" of the Users Handbook.
                //
                //
                // "ADXₚ|ₜQ" should be equivalent to "ADXₚ{Qₜ}*".
                // (Note that in the real pipe construct the "|" is
                // itself in subscript).  During parsing, the values
                // of Q and ₜ were combined into the two parts of the
                // rc_word_value tuple.  We evaluate Qₜ as
                // rc_word_val.
                let (base, index) = rc_word_value.as_ref();
                let base_value = base.evaluate(target_address, symtab, rc_allocator, op)?;
                let index_value = index.evaluate(target_address, symtab, rc_allocator, op)?;
                let rc_word_val: Unsigned36Bit = combine_fragment_values(base_value, index_value);
                let p_value: Unsigned36Bit =
                    index_value_of(p.evaluate(target_address, symtab, rc_allocator, op)?);
                let addr: Address = rc_allocator.allocate(*rc_word_span, rc_word_val);
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
pub(crate) enum Commas {
    One(Span),
    Two(Span),
    Three(Span),
}

impl Commas {
    pub(crate) fn span(&self) -> &Span {
        match &self {
            Commas::One(span) | Commas::Two(span) | Commas::Three(span) => span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CommasOrInstruction {
    I(UntaggedProgramInstruction),
    C(Option<Commas>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommaDelimitedInstruction {
    pub(crate) leading_commas: Option<Commas>,
    pub(crate) instruction: UntaggedProgramInstruction,
    pub(crate) trailing_commas: Option<Commas>,
}

impl CommaDelimitedInstruction {
    fn new(
        leading_commas: Option<Commas>,
        instruction: UntaggedProgramInstruction,
        trailing_commas: Option<Commas>,
    ) -> Self {
        Self {
            leading_commas,
            instruction,
            trailing_commas,
        }
    }

    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.instruction.symbol_uses(block_id, block_offset)
    }

    pub(crate) fn span(&self) -> Span {
        let start = self
            .leading_commas
            .as_ref()
            .map(|c| c.span().start)
            .unwrap_or(self.instruction.span.start);
        let end = self
            .trailing_commas
            .as_ref()
            .map(|c| c.span().end)
            .unwrap_or(self.instruction.span.end);
        Span::from(start..end)
    }
}

impl Evaluate for CommaDelimitedInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction
            .evaluate(target_address, symtab, rc_allocator, op)
            .map(|value| comma_transformation(&self.leading_commas, value, &self.trailing_commas))
    }
}

/// Implement the value transformation rules described in the table
/// "COMMA CHART" in section 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS"
/// of the Users Handbook.
///
/// It's likely that the TX-2's original implementation of this in the
/// M4 assembler used the system configuration feature to perform the
/// word-quarter masking and mapping.  While we could do that it would
/// introduce a dependency between the assembler and the siimulator's
/// implementation of the exchange unit.  Generating the correct
/// system configuration value would be more or less as complex as
/// just implementing the logic here, so we just implement it here in
/// order to avoid the dependency.
fn comma_transformation(
    leading_commas: &Option<Commas>,
    value: Unsigned36Bit,
    trailing_commas: &Option<Commas>,
) -> Unsigned36Bit {
    match (leading_commas, trailing_commas) {
        (None, None) => value,
        (None, Some(Commas::One(_))) => value.and(0o777).shl(27),
        (None, Some(Commas::Two(_))) => value.and(0o777777).shl(18),
        (None, Some(Commas::Three(_))) => value.and(0o777777777).shl(9),

        (Some(Commas::One(_)), None) => value.and(0o777),
        (Some(Commas::One(_)), Some(Commas::One(_))) => value.and(0o777_777).shl(9),
        (Some(Commas::One(_)), Some(Commas::Two(_))) => value.and(0o777).shl(18),
        (Some(Commas::One(_)), Some(Commas::Three(_))) => value.and(0o777_777_777_000),

        (Some(Commas::Two(_)), None) => value.and(0o777_777),
        (Some(Commas::Two(_)), Some(Commas::One(_))) => value.and(0o777).shl(9),
        (Some(Commas::Two(_)), Some(Commas::Two(_))) => {
            let hi = value.and(0o000_000_777_777).shl(18);
            let lo = value.and(0o777_777_000_000).shr(18);
            hi | lo
        }
        (Some(Commas::Two(_)), Some(Commas::Three(_))) => value.and(0o777_777_000_000).shr(18),

        (Some(Commas::Three(_)), None) => value.and(0o777),
        (Some(Commas::Three(_)), Some(Commas::One(_))) => value.and(0o777_000_000_000).shr(27),
        (Some(Commas::Three(_)), Some(Commas::Two(_))) => value.and(0o777_000_000_000).shr(9),
        (Some(Commas::Three(_)), Some(Commas::Three(_))) => value.and(0o777_777_000_000).shr(18),
    }
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
                    LiteralValue {
                        span,
                        elevation: Script::Normal,
                        value: Unsigned36Bit::ZERO,
                    },
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

#[cfg(test)]
mod comma_tests {
    use super::super::span::*;
    use super::comma_transformation;
    use super::instructions_with_comma_counts as parent_instructions_with_comma_counts;
    use super::CommaDelimitedInstruction;
    use super::Commas;
    use super::CommasOrInstruction;
    use super::UntaggedProgramInstruction;
    use base::u36;
    use std::fmt::Formatter;

    #[derive(Clone, Eq)]
    struct Briefly(CommaDelimitedInstruction);

    impl From<(Option<Commas>, UntaggedProgramInstruction, Option<Commas>)> for Briefly {
        fn from(value: (Option<Commas>, UntaggedProgramInstruction, Option<Commas>)) -> Self {
            Self(CommaDelimitedInstruction::new(value.0, value.1, value.2))
        }
    }

    fn briefly(
        v: Vec<(Option<Commas>, UntaggedProgramInstruction, Option<Commas>)>,
    ) -> Vec<Briefly> {
        v.into_iter().map(Briefly::from).collect()
    }

    impl PartialEq<CommaDelimitedInstruction> for Briefly {
        fn eq(&self, other: &CommaDelimitedInstruction) -> bool {
            self == other
        }
    }

    impl PartialEq<Briefly> for Briefly {
        fn eq(&self, other: &Briefly) -> bool {
            self.0 == other.0
        }
    }

    fn instructions_with_comma_counts(input: Vec<CommasOrInstruction>) -> Vec<Briefly> {
        dbg!(&input);
        let output = parent_instructions_with_comma_counts(input.into_iter());
        output.into_iter().map(Briefly).collect()
    }

    impl std::fmt::Debug for Briefly {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            use super::*;
            let instr_string: String = {
                match &self.0.instruction.inst {
                    InstructionFragment::Arithmetic(ArithmeticExpression { first, tail }) => {
                        if tail.is_empty() {
                            match first {
                                Atom::Literal(LiteralValue {
                                    span,
                                    elevation: Script::Normal,
                                    value,
                                }) => {
                                    format!("span={span:?}, value={value}")
                                }
                                _ => unreachable!(),
                            }
                        } else {
                            unreachable!();
                        }
                    }
                    _ => unreachable!(),
                }
            };
            write!(
                f,
                "({:?},UntaggedProgramInstruction({instr_string}),{:?})",
                self.0.leading_commas, self.0.trailing_commas
            )
        }
    }

    fn inst(sp: Span, n: u16) -> UntaggedProgramInstruction {
        use super::*;
        UntaggedProgramInstruction {
            span: sp,
            holdbit: HoldBit::Unspecified,
            inst: InstructionFragment::from(ArithmeticExpression::from(Atom::Literal(
                LiteralValue {
                    span: sp,
                    elevation: Script::Normal,
                    value: n.into(),
                },
            ))),
        }
    }

    #[test]
    fn test_instructions_with_comma_counts_len_0_with_0_instructions() {
        assert_eq!(instructions_with_comma_counts(Vec::new()), briefly(vec![]))
    }

    #[test]
    fn test_instructions_with_comma_counts_len_1_with_1_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::I(inst(span(0..1), 1))]),
            briefly(vec![(None, inst(span(0..1), 1), None),])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_1_with_0_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![CommasOrInstruction::C(Some(Commas::One(span(
                0..1
            ))))]),
            briefly(vec![]),
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_0_instructions() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(Some(Commas::One(span(0..1)))),
                CommasOrInstruction::C(Some(Commas::Two(span(3..5)))),
            ]),
            briefly(vec![(
                Some(Commas::One(span(0..1))),
                inst(span(3..3), 0),
                Some(Commas::Two(span(3..5))),
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_a() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::I(inst(span(0..1), 1)),
                CommasOrInstruction::C(Some(Commas::One(span(1..2)))),
            ]),
            briefly(vec![(
                None,
                inst(span(0..1), 1),
                Some(Commas::One(span(1..2))),
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_1_instruction_b() {
        assert_eq!(
            instructions_with_comma_counts(vec![
                CommasOrInstruction::C(Some(Commas::Two(span(0..2)))),
                CommasOrInstruction::I(inst(span(2..3), 3)),
            ]),
            briefly(vec![(
                Some(Commas::Two(span(0..2))),
                inst(span(2..3), 3),
                None,
            )])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_2_with_2_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![I(inst(span(0..1), 1)), I(inst(span(2..3), 2))]),
            briefly(vec![
                (None, inst(span(0..1), 1), None),
                (None, inst(span(2..3), 2), None,),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_0_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                C(Some(Commas::Two(span(2..3)))),
                C(Some(Commas::Three(span(4..5)))),
            ]),
            briefly(vec![
                (
                    Some(Commas::One(span(0..1))),
                    inst(span(2..2), 0),
                    Some(Commas::Two(span(2..3))),
                ),
                (
                    Some(Commas::Two(span(2..3))),
                    inst(span(4..4), 0),
                    Some(Commas::Three(span(4..5))),
                ),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_1_instructions() {
        use CommasOrInstruction::*;
        // CCI cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                C(Some(Commas::Two(span(2..3)))),
                I(inst(span(3..4), 3))
            ]),
            briefly(vec![
                (
                    Some(Commas::One(span(0..1))),
                    inst(span(2..2), 0),
                    Some(Commas::Two(span(2..3))),
                ),
                (Some(Commas::Two(span(2..3))), inst(span(3..4), 3), None,),
            ])
        );

        // CIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                I(inst(span(1..2), 2)),
                C(Some(Commas::One(span(2..3)))),
            ]),
            briefly(vec![(
                Some(Commas::One(span(0..1))),
                inst(span(1..2), 2),
                Some(Commas::One(span(2..3))),
            )])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::One(span(0..1)))),
                I(inst(span(1..2), 2)),
                C(Some(Commas::Three(span(2..3))))
            ]),
            briefly(vec![(
                Some(Commas::One(span(0..1))),
                inst(span(1..2), 2),
                Some(Commas::Three(span(2..3))),
            )])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(None),
                I(inst(span(0..1), 2)),
                C(Some(Commas::Three(span(1..4))))
            ]),
            briefly(vec![(
                None,
                inst(span(0..1), 2),
                Some(Commas::Three(span(1..4)))
            )])
        );

        // ICC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                C(Some(Commas::One(span(1..2)))), // 2..3 is a space
                C(Some(Commas::Two(span(3..4))))
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), Some(Commas::One(span(1..2)))),
                (
                    Some(Commas::One(span(1..2))),
                    inst(span(3..3), 0),
                    Some(Commas::Two(span(3..4)))
                )
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(
                // "1,, ,,,"
                vec![
                    I(inst(span(0..1), 1)),
                    C(Some(Commas::Two(span(1..3)))),
                    C(Some(Commas::Three(span(4..7))))
                ]
            ),
            briefly(vec![
                (None, inst(span(0..1), 1), Some(Commas::Two(span(1..3)))),
                (
                    Some(Commas::Two(span(1..3))),
                    inst(span(4..4), 0),
                    Some(Commas::Three(span(4..7)))
                ),
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_2_instructions() {
        use CommasOrInstruction::*;
        // IIC cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                I(inst(span(2..3), 2)),
                C(Some(Commas::Two(span(3..5)))),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), None),
                (None, inst(span(2..3), 2), Some(Commas::Two(span(3..5)))),
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                // span 1..2 is a space.
                I(inst(span(2..3), 2)),
                C(None)
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), None,),
                (None, inst(span(2..3), 2), None,)
            ])
        );

        // ICI cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                C(Some(Commas::Two(span(1..3)))),
                I(inst(span(3..4), 2)),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), Some(Commas::Two(span(1..3)))),
                (Some(Commas::Two(span(1..3))), inst(span(3..4), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                C(Some(Commas::Three(span(1..4)))),
                I(inst(span(4..5), 2)),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), Some(Commas::Three(span(1..4)))),
                (Some(Commas::Three(span(1..4))), inst(span(4..5), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                C(Some(Commas::One(span(1..2)))),
                I(inst(span(2..3), 2)),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), Some(Commas::One(span(1..2)))),
                (Some(Commas::One(span(1..2))), inst(span(2..3), 2), None)
            ])
        );

        // CII cases
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(Some(Commas::Two(span(0..2)))),
                I(inst(span(2..3), 1)),
                I(inst(span(4..5), 2)),
            ]),
            briefly(vec![
                (Some(Commas::Two(span(0..2))), inst(span(2..3), 1), None),
                (None, inst(span(4..5), 2), None)
            ])
        );
        assert_eq!(
            instructions_with_comma_counts(vec![
                C(None),
                I(inst(span(0..1), 1)),
                I(inst(span(1..3), 2)),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), None),
                (None, inst(span(1..3), 2), None)
            ])
        );
    }

    #[test]
    fn test_instructions_with_comma_counts_len_3_with_3_instructions() {
        use CommasOrInstruction::*;
        assert_eq!(
            instructions_with_comma_counts(vec![
                I(inst(span(0..1), 1)),
                I(inst(span(2..3), 2)),
                I(inst(span(4..5), 3)),
            ]),
            briefly(vec![
                (None, inst(span(0..1), 1), None),
                (None, inst(span(2..3), 2), None),
                (None, inst(span(4..5), 3), None),
            ])
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_0() {
        assert_eq!(
            comma_transformation(&None, u36!(0o444_333_222_111), &None),
            u36!(0o444_333_222_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16)))
            ),
            u36!(0o111_000_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17)))
            ),
            u36!(0o222_111_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_0_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &None,
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18)))
            ),
            u36!(0o333_222_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_000_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_222_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o000_111_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_1_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::One(span(2..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o444_333_222_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_222_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_000_111_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o222_111_444_333)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_2_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Two(span(1..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o000_000_444_333)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_0() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &None,
            ),
            u36!(0o000_000_000_111)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_1() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::One(span(15..16))),
            ),
            u36!(0o000_000_000_444)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_2() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Two(span(15..17))),
            ),
            u36!(0o000_444_000_000)
        );
    }

    // This test case is taken from the table "COMMA CHART" in section
    // 6-2.4, "NUMERICAL FORMAT - USE OF COMMAS" of the Users
    // Handbook.
    #[test]
    fn test_comma_transformation_3_3() {
        // For convenience, our comma test cases adopt a standard
        // (imaginary) layout for the input.  We do this so that the
        // input spans could conceivably have been generated by real
        // input, so that our tests don't inadvertently require the
        // implementation to allow inconsistent/invalid inputs.
        //
        // Span 0..3 is the initial commas (or spaces).
        // Span 3..15 is the constant 444333222111.
        // Span 15..18 is the trailing commas (or spaces).
        assert_eq!(
            comma_transformation(
                &Some(Commas::Three(span(0..3))),
                u36!(0o444_333_222_111),
                &Some(Commas::Three(span(15..18))),
            ),
            u36!(0o000_000_444_333)
        );
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EqualityValue(Vec<CommaDelimitedInstruction>);

impl EqualityValue {
    pub(crate) fn items(&self) -> &[CommaDelimitedInstruction] {
        &self.0
    }
}

impl From<Vec<CommaDelimitedInstruction>> for EqualityValue {
    fn from(value: Vec<CommaDelimitedInstruction>) -> Self {
        Self(value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UntaggedProgramInstruction {
    pub(crate) span: Span,
    pub(crate) holdbit: HoldBit,
    pub(crate) inst: InstructionFragment,
}

impl UntaggedProgramInstruction {
    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.inst.symbol_uses(block_id, block_offset)
    }
}

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        // TODO: issue a diagnostic if a TaggedProgramInstruction
        // contains inconsistent values for the hold bit.  We will need to decide
        // whether something like ",h" sets the hold bit (i.e. whether
        // the hold bit is supposed to be subject to the same
        // comma rules that other values are).
        self.inst
            .evaluate(target_address, symtab, rc_allocator, op)
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
    pub(crate) instructions: Vec<CommaDelimitedInstruction>,
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
        for inst in self.instructions.iter() {
            result.extend(inst.symbol_uses(block_id, offset));
        }
        result.into_iter()
    }

    pub(crate) fn span(&self) -> Span {
        let begin = match self.tag() {
            Some(t) => t.span.start,
            None => {
                self.instructions
                    .first()
                    .expect("TaggedProgramInstruction must contain at least one instruction")
                    .span()
                    .start
            }
        };
        let end = self
            .instructions
            .last()
            .expect("TaggedProgramInstruction must contain at least one instruction")
            .span()
            .end;
        Span::from(begin..end)
    }

    pub(crate) fn tag(&self) -> Option<&Tag> {
        self.tag.as_ref()
    }

    pub(crate) fn single(
        tag: Option<Tag>,
        instruction: UntaggedProgramInstruction,
    ) -> TaggedProgramInstruction {
        TaggedProgramInstruction::multiple(
            tag,
            vec![CommaDelimitedInstruction {
                leading_commas: None,
                instruction,
                trailing_commas: None,
            }],
        )
    }

    pub(crate) fn multiple(
        tag: Option<Tag>,
        instructions: Vec<CommaDelimitedInstruction>,
    ) -> TaggedProgramInstruction {
        assert!(!instructions.is_empty());
        TaggedProgramInstruction { tag, instructions }
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
    Assignment(Span, SymbolName, EqualityValue), // User Guide calls these "equalities".
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
                inst: InstructionFragment::from(ArithmeticExpression::from(Atom::Literal(
                    LiteralValue {
                        span,
                        elevation: Script::Normal,
                        value,
                    },
                ))),
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
