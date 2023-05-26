///! Abstract syntax representation.   It's mostly not actually a tree.
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;
use std::ops::Shl;

use chumsky::span::Span as _;

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use crate::eval::{HereValue, SymbolLookupFailure, SymbolValue};

use super::eval::{Evaluate, SymbolContext, SymbolDefinition, SymbolLookup, SymbolUse};
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::types::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Elevated<T> {
    inner: T,
    script: Script,
}

impl<T> From<(Script, T)> for Elevated<T> {
    fn from((script, inner): (Script, T)) -> Elevated<T> {
        Elevated { inner, script }
    }
}

pub(crate) fn elevate<T>(script: Script, inner: T) -> Elevated<T> {
    Elevated { script, inner }
}

pub(crate) fn elevate_super<T>(inner: T) -> Elevated<T> {
    elevate(Script::Super, inner)
}

pub(crate) fn elevate_sub<T>(inner: T) -> Elevated<T> {
    elevate(Script::Sub, inner)
}

pub(crate) fn elevate_normal<T>(inner: T) -> Elevated<T> {
    elevate(Script::Normal, inner)
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

    #[cfg(test)]
    pub(crate) fn span(&self) -> &Span {
        &self.span
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<S: SymbolLookup>(
        &self,
        _target_address: &HereValue,
        _symtab: &mut S,
        _op: &mut S::Operation<'_>,
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

// TODO: avoid the panics from this function.
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
                    Err(e) => {
                        panic!("cannot find superscript equivalent of '{ch}': {e}");
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
                    Err(e) => {
                        panic!("cannot find superscript equivalent of '{ch}': {e}");
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
    LogicalOr, // "union" in the Users Handbook
}

/// A molecule is an arithmetic expression all in normal script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArithmeticExpression {
    first: Atom,
    tail: Vec<(Operator, Atom)>,
}

impl From<Atom> for ArithmeticExpression {
    fn from(a: Atom) -> ArithmeticExpression {
        ArithmeticExpression {
            first: a,
            tail: Vec::new(),
        }
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
            Operator::LogicalOr => left.bitor(right.into()),
        }
    }
}

impl Evaluate for ArithmeticExpression {
    fn evaluate<S: SymbolLookup>(
        &self,
        target_address: &HereValue,
        symtab: &mut S,
        op: &mut S::Operation<'_>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn fold_step<S: SymbolLookup>(
            acc: Result<Unsigned36Bit, SymbolLookupFailure>,
            (binop, right): &(Operator, Atom),
            target_address: &HereValue,
            symtab: &mut S,
            op: &mut S::Operation<'_>,
        ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
            let right: Unsigned36Bit = right.evaluate(target_address, symtab, op)?;
            Ok(ArithmeticExpression::eval_binop(acc?, binop, right))
        }

        let first: Unsigned36Bit = self.first.evaluate(target_address, symtab, op)?;
        let result: Result<Unsigned36Bit, SymbolLookupFailure> =
            self.tail.iter().fold(Ok(first), |acc, curr| {
                fold_step(acc, curr, target_address, symtab, op)
            });
        result
    }
}

/// Eventually we will support real expressions, but for now we only
/// suport literals and references to symbols ("equalities" in the
/// User Handbook).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Atom {
    Literal(LiteralValue),
    Symbol(Span, Script, SymbolName),
    Here(Script), // the special symbol '#'.
}

impl Atom {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Atom::Literal(_) | Atom::Here(_) => (),
            Atom::Symbol(span, script, symbol_name) => {
                result.push((
                    symbol_name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                ));
            }
        }
        result.into_iter()
    }
}

impl Evaluate for Atom {
    fn evaluate<S: SymbolLookup>(
        &self,
        target_address: &HereValue,
        symtab: &mut S,
        op: &mut S::Operation<'_>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            Atom::Here(elevation) => match target_address {
                HereValue::Address(addr) => {
                    let value: Unsigned36Bit = (*addr).into();
                    Ok(value.shl(elevation.shift()))
                }
                HereValue::NotAllowed => {
                    todo!("# is not allowed in origins")
                }
            },
            Atom::Literal(literal) => Ok(literal.value()),
            Atom::Symbol(span, elevation, name) => {
                let context = SymbolContext::from((elevation, *span));
                match symtab.lookup_with_op(name, *span, target_address, &context, op) {
                    Ok(SymbolValue::Final(value)) => Ok(value),
                    Err(e) => Err(e),
                }
                .map(|value| value.shl(elevation.shift()))
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
            Atom::Here(Script::Super) => f.write_str("@super_hash@"),
            Atom::Here(Script::Normal) => f.write_char('#'),
            Atom::Here(Script::Sub) => f.write_str("@sub_hash@"),
            Atom::Literal(value) => value.fmt(f),
            Atom::Symbol(_span, elevation, name) => {
                elevated_string(&name.to_string(), elevation).fmt(f)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum InstructionFragment {
    /// Arithmetic expressions are permitted in normal case accorfind
    /// to the Users Handbook, but currently this implementation
    /// allows them in subscript/superscript too.
    Arithmetic(ArithmeticExpression),
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
        }
        result.into_iter()
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<S: SymbolLookup>(
        &self,
        target_address: &HereValue,
        symtab: &mut S,
        op: &mut S::Operation<'_>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            InstructionFragment::Arithmetic(expr) => expr.evaluate(target_address, symtab, op),
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
        block: usize,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Origin::Literal(_span, _) => (),
            Origin::Symbolic(span, name) => {
                result.push((name.clone(), *span, SymbolUse::Origin(name.clone(), block)))
            }
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

impl Evaluate for UntaggedProgramInstruction {
    fn evaluate<S: SymbolLookup>(
        &self,
        target_address: &HereValue,
        symtab: &mut S,
        op: &mut S::Operation<'_>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        fn or_looked_up_value<S: SymbolLookup>(
            accumulator: Result<Unsigned36Bit, SymbolLookupFailure>,
            frag: &InstructionFragment,
            target_address: &HereValue,
            symtab: &mut S,
            op: &mut S::Operation<'_>,
        ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
            accumulator.and_then(|acc| Ok(acc | frag.evaluate(target_address, symtab, op)?))
        }

        self.parts
            .iter()
            .fold(Ok(Unsigned36Bit::ZERO), |acc, curr| {
                or_looked_up_value(acc, curr, target_address, symtab, op)
            })
            .map(|word| match self.holdbit {
                HoldBit::Hold => word | HELD_MASK,
                HoldBit::NotHold => word & !HELD_MASK,
                HoldBit::Unspecified => word,
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Tag {
    pub(crate) name: SymbolName,
    pub(crate) span: Span,
}

impl Tag {
    pub(crate) fn symbol_uses(
        &self,
        block_number: usize,
        block_offset: usize,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        [(
            self.name.clone(),
            self.span,
            SymbolUse::Definition(SymbolDefinition::Tag {
                block_number,
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
        block: usize,
        offset: usize,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::new();
        if let Some(tag) = self.tag.as_ref() {
            result.extend(tag.symbol_uses(block, offset));
        }
        result.extend(self.instruction.symbol_uses());
        result.into_iter()
    }
}

impl Evaluate for TaggedProgramInstruction {
    fn evaluate<S: SymbolLookup>(
        &self,
        target_address: &HereValue,
        symtab: &mut S,
        op: &mut S::Operation<'_>,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        self.instruction.evaluate(target_address, symtab, op)
    }
}

const HELD_MASK: Unsigned36Bit = u36!(1 << 35);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    pub(crate) blocks: Vec<ManuscriptBlock>,
}

impl SourceFile {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.blocks
            .iter()
            .enumerate()
            .flat_map(|(block_number, block)| block.symbol_uses(block_number))
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptLine {
    MetaCommand(ManuscriptMetaCommand),
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
            Statement::Instruction(TaggedProgramInstruction { tag, instruction }) => {
                if let Some(t) = tag {
                    Span::from(t.span.start()..instruction.span.end())
                } else {
                    instruction.span
                }
            }
        }
    }

    fn memory_size(&self) -> usize {
        match self {
            Statement::Assignment(_, _, _) => 0,
            Statement::Instruction(_) => 1,
        }
    }

    pub(crate) fn symbol_uses(
        &self,
        block: usize,
        offset: usize,
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
            Statement::Instruction(inst) => inst.symbol_uses(block, offset).collect(),
        }
        .into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ManuscriptBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) statements: Vec<Statement>,
}

impl ManuscriptBlock {
    pub(crate) fn symbol_uses(
        &self,
        block_number: usize,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::new();
        if let Some(origin) = self.origin.as_ref() {
            result.extend(origin.symbol_uses(block_number));
        }
        for (offset, statement) in self.statements.iter().enumerate() {
            result.extend(statement.symbol_uses(block_number, offset));
        }
        result.into_iter()
    }

    pub(crate) fn instruction_count(&self) -> usize {
        self.statements.iter().map(|st| st.memory_size()).sum()
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

#[derive(Debug, Default)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: Vec<Block>,
    entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn instruction_count(&self) -> usize {
        self.blocks.iter().map(Block::instruction_count).sum()
    }

    pub(crate) fn set_entry_point(&mut self, a: Address) {
        self.entry_point = Some(a)
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }

    pub(crate) fn push(&mut self, block: Block) {
        self.blocks.push(block)
    }

    pub(crate) fn blocks(&self) -> impl Iterator<Item = &Block> {
        self.blocks.iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) origin: Option<Origin>,
    pub(crate) location: Option<Address>,
    pub(crate) items: Vec<TaggedProgramInstruction>,
}

impl Block {
    pub(crate) fn push(&mut self, inst: TaggedProgramInstruction) {
        self.items.push(inst);
    }

    pub(crate) fn instruction_count(&self) -> usize {
        self.items.len()
    }
}
