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
use crate::symtab::{LookupOperation, RcAllocator, RcBlock};

use super::eval::{Evaluate, SymbolContext, SymbolDefinition, SymbolLookup, SymbolUse};
use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::symtab::SymbolTable;
use super::types::{
    offset_from_origin, AssemblerFailure, BlockIdentifier, MachineLimitExceededFailure, Span,
};

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

/// Eventually we will support real expressions, but for now we only
/// suport literals and references to symbols ("equalities" in the
/// User Handbook).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Atom {
    Literal(LiteralValue),
    Symbol(Span, Script, SymbolName),
    Here(Script), // the special symbol '#'.
    Parens(Box<ArithmeticExpression>),
    RcRef(Span, Box<ArithmeticExpression>),
}

impl Atom {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Atom::Literal(_) | Atom::Here(_) | Atom::RcRef(_, _) => (),
            Atom::Symbol(span, script, symbol_name) => {
                result.push((
                    symbol_name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                ));
            }
            Atom::Parens(expr) => {
                result.extend(expr.symbol_uses());
            }
        }
        result.into_iter()
    }
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
                match symtab.lookup_with_op(name, *span, target_address, rc_allocator, &context, op)
                {
                    Ok(SymbolValue::Final(value)) => Ok(value),
                    Err(e) => Err(e),
                }
                .map(|value| value.shl(elevation.shift()))
            }
            Atom::Parens(expr) => expr.evaluate(target_address, symtab, rc_allocator, op),
            Atom::RcRef(span, content) => {
                let value: Unsigned36Bit =
                    content.evaluate(target_address, symtab, rc_allocator, op)?;
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
            Atom::Here(Script::Super) => f.write_str("@super_hash@"),
            Atom::Here(Script::Normal) => f.write_char('#'),
            Atom::Here(Script::Sub) => f.write_str("@sub_hash@"),
            Atom::Literal(value) => value.fmt(f),
            Atom::Symbol(_span, elevation, name) => {
                elevated_string(&name.to_string(), elevation).fmt(f)
            }
            Atom::Parens(expr) => {
                write!(f, "({expr})")
            }
            Atom::RcRef(_span, _rc_reference) => {
                // The RcRef doesn't itself record the content of the
                // {...} because that goes into the rc-block itself.
                write!(f, "{{...}}")
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
    fn evaluate<R: RcAllocator>(
        &self,
        target_address: &HereValue,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
        op: &mut LookupOperation,
    ) -> Result<Unsigned36Bit, SymbolLookupFailure> {
        match self {
            InstructionFragment::Arithmetic(expr) => {
                expr.evaluate(target_address, symtab, rc_allocator, op)
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
    fn evaluate<R: RcAllocator>(
        &self,
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
            Ok(accumulator | frag.evaluate(target_address, symtab, rc_allocator, op)?)
        }

        self.parts
            .iter()
            .try_fold(Unsigned36Bit::ZERO, |acc, curr| {
                or_looked_up_value(acc, curr, target_address, symtab, rc_allocator, op)
            })
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
        if let Some(tag) = self.tag.as_ref() {
            result.extend(tag.symbol_uses(block_id, offset));
        }
        result.extend(self.instruction.symbol_uses());
        result.into_iter()
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

pub(crate) fn bad_offset(block_id: BlockIdentifier, offset: usize) -> AssemblerFailure {
    AssemblerFailure::MachineLimitExceeded(MachineLimitExceededFailure::BlockTooLarge {
        block_id,
        offset,
    })
}

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

    //pub(crate) fn define_rc_word(
    //    &mut self,
    //    value: TaggedProgramInstruction,
    //) -> Result<RcReference, AssemblerFailure> {
    //    let rcblock: &mut ManuscriptBlock = self
    //        .blocks
    //        .entry(BlockIdentifier::RcWords)
    //        .or_insert_with(|| ManuscriptBlock {
    //            origin: None,
    //            statements: Vec::new(),
    //        });
    //    let offset = rcblock.statements.len();
    //    match Unsigned18Bit::try_from(offset) {
    //        Ok(id) => {
    //            rcblock.statements.push(Statement::Instruction(value));
    //            Ok(RcReference::new(id))
    //        }
    //        Err(_) => Err(bad_offset(BlockIdentifier::RcWords, offset)),
    //    }
    //}

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
    RcWord(Span, Unsigned36Bit),
}

impl Statement {
    fn span(&self) -> Span {
        match self {
            Statement::RcWord(span, _) => *span,
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

    fn emitted_instruction_count(&self) -> Unsigned18Bit {
        match self {
            Statement::Assignment(_, _, _) => Unsigned18Bit::ZERO,
            Statement::Instruction(_) | Statement::RcWord(_, _) => Unsigned18Bit::ONE,
        }
    }

    pub(crate) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        match self {
            Statement::RcWord(_, _) => Vec::new(),
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

/// impl MacroDefinition {
///     pub(crate) fn emitted_instruction_count(&self) -> Unsigned18Bit {
///         self.body.iter().map(|stmt| stmt.memory_size()).sum()
///     }
/// }

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
        fn make_rc_block(max_occupied_addr: Option<Address>) -> LocatedBlock {
            let rc_block_address: Address =
                max_occupied_addr.unwrap_or_else(|| Origin::default_address());
            LocatedBlock {
                location: rc_block_address,
                items: Vec::new(),
            }
        }
        self.blocks
            .remove(&BlockIdentifier::RcWords)
            .unwrap_or_else(|| make_rc_block(max_occupied_addr))
            .into()
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }
}

impl RcAllocator for Directive {
    fn allocate(&mut self, span: Span, value: Unsigned36Bit) -> Address {
        match self.blocks.get_mut(&BlockIdentifier::RcWords) {
            None => {
                panic!(
                    "precondition did not hold: no RC-word block was allocated in the directive"
                );
            }
            Some(rc_word_block) => match Unsigned18Bit::try_from(rc_word_block.items.len()) {
                Ok(offset) => {
                    let addr = rc_word_block.location.index_by(offset);
                    rc_word_block.items.push(Statement::RcWord(span, value));
                    addr
                }
                Err(_) => {
                    unimplemented!("handle overflow")
                }
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) origin: Option<Origin>,
    pub(crate) location: Option<Address>,
    pub(crate) items: Vec<Statement>,
}

impl Block {
    pub(crate) fn emitted_instruction_count(&self) -> Unsigned18Bit {
        self.items
            .iter()
            .map(|stmt| stmt.emitted_instruction_count())
            .sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedBlock {
    pub(crate) location: Address,
    pub(crate) items: Vec<Statement>,
}

impl LocatedBlock {
    pub(crate) fn get_offset(
        &self,
        block_id: BlockIdentifier,
        offset: usize,
    ) -> Result<Address, AssemblerFailure> {
        if let Ok(h) = Unsigned18Bit::try_from(offset)
            .map_err(|_| ())
            .and_then(|n| offset_from_origin(&self.location, n).map_err(|_| ()))
        {
            Ok(h)
        } else {
            Err(bad_offset(block_id, offset))
        }
    }

    pub(crate) fn following_addr(&self) -> Address {
        self.location.index_by(self.emitted_instruction_count())
    }

    pub(crate) fn emitted_instruction_count(&self) -> Unsigned18Bit {
        self.items
            .iter()
            .map(|stmt| stmt.emitted_instruction_count())
            .sum()
    }
}
