//! Abstract syntax representation.   It's mostly not actually a tree.
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use super::glyph;
use super::lexer::Token;
use super::span::*;
use super::state::NumeralMode;
use super::symbol::{SymbolContext, SymbolName};
use super::symtab::{BadSymbolDefinition, SymbolDefinition, SymbolTable, TagDefinition};
use super::types::*;

#[derive(Debug, PartialEq, Eq, Clone)]
enum SymbolUse {
    Reference(SymbolContext),
    Definition(SymbolDefinition),
    Origin(SymbolName, BlockIdentifier),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum RcWordAllocationFailure {
    RcBlockTooBig {
        source: RcWordSource,
        rc_block_len: usize,
    },
    InconsistentTag(BadSymbolDefinition),
}

impl Display for RcWordAllocationFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RcWordAllocationFailure::RcBlockTooBig {
                source,
                rc_block_len,
            } => {
                write!(f, "failed to allocate RC word for {source}; RC block is already {rc_block_len} words long")
            }
            RcWordAllocationFailure::InconsistentTag(e) => {
                let name = e.symbol();
                write!(
                    f,
                    "failed to define tag {name} because it already had a previous definition: {e}"
                )
            }
        }
    }
}

impl Error for RcWordAllocationFailure {}

pub(crate) trait RcAllocator {
    fn allocate(
        &mut self,
        source: RcWordSource,
        value: Unsigned36Bit,
    ) -> Result<Address, RcWordAllocationFailure>;
}

pub(crate) trait RcUpdater {
    fn update(&mut self, address: Address, value: Unsigned36Bit);
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
    pub(crate) fn unshifted_value(&self) -> Unsigned36Bit {
        self.value
    }
}

impl Spanned for LiteralValue {
    fn span(&self) -> Span {
        self.span
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SignedAtom {
    pub(super) negated: bool,
    pub(super) span: Span,
    pub(super) magnitude: Atom,
}

impl From<Atom> for SignedAtom {
    fn from(magnitude: Atom) -> Self {
        Self {
            negated: false,
            span: magnitude.span(),
            magnitude,
        }
    }
}

impl SignedAtom {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        self.magnitude.symbol_uses(block_id, block_offset)
    }
}

impl Spanned for SignedAtom {
    fn span(&self) -> Span {
        self.span
    }
}

impl std::fmt::Display for SignedAtom {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.negated {
            write!(f, "-{}", self.magnitude)
        } else {
            write!(f, "{}", self.magnitude)
        }
    }
}

/// A molecule is an arithmetic expression all in normal script.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArithmeticExpression {
    pub(crate) first: SignedAtom,
    pub(crate) tail: Vec<(Operator, SignedAtom)>,
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

impl From<SignedAtom> for ArithmeticExpression {
    fn from(a: SignedAtom) -> ArithmeticExpression {
        ArithmeticExpression {
            first: a,
            tail: Vec::new(),
        }
    }
}

impl From<Atom> for ArithmeticExpression {
    fn from(a: Atom) -> ArithmeticExpression {
        ArithmeticExpression::from(SignedAtom::from(a))
    }
}

impl From<SymbolOrLiteral> for ArithmeticExpression {
    fn from(value: SymbolOrLiteral) -> Self {
        ArithmeticExpression::from(Atom::from(value))
    }
}

impl Spanned for ArithmeticExpression {
    fn span(&self) -> Span {
        let start = self.first.span().start;
        let end = self
            .tail
            .last()
            .map(|(_op, atom)| atom.span().end)
            .unwrap_or(self.first.span().end);
        span(start..end)
    }
}

impl ArithmeticExpression {
    pub(crate) fn with_tail(
        first: SignedAtom,
        tail: Vec<(Operator, SignedAtom)>,
    ) -> ArithmeticExpression {
        ArithmeticExpression { first, tail }
    }

    fn symbol_uses(
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

    pub(crate) fn eval_binop(
        left: Unsigned36Bit,
        binop: &Operator,
        right: Unsigned36Bit,
    ) -> Unsigned36Bit {
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
                    todo!("subtraction overflow occurred in {left}-{right} but this is not implemented")
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

/// A configuration syllable can be specified by putting it in a
/// superscript, or by putting it in normal script after a ‖ symbol
/// (‖x or ‖2, for example).  This is described in section 6-2.1 of
/// the Users Handbook.
///
/// In the description of the parts of an instruction (section 6-2.1,
/// "INSTRUCTION WORDS" of the Users Handbook) we see the
/// specification that the configuration syllable cannot contain any
/// spaces.  But this doesn't prevent the config syllable containing,
/// say, an arithmetic expression.  Indeed, Leonard Kleinrock's
/// program for network similation does exactly that (by using a
/// negated symbol as a configuration value).
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConfigValue {
    pub(crate) already_superscript: bool,
    pub(crate) expr: ArithmeticExpression,
}

impl ConfigValue {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let used_as_config = SymbolUse::Reference(SymbolContext::configuration());
        self.expr
            .symbol_uses(block_id, block_offset)
            .map(move |(name, span, _ignore_symbol_use)| (name, span, used_as_config.clone()))
    }
}

impl Spanned for ConfigValue {
    fn span(&self) -> Span {
        self.expr.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistersContaining(Vec<RegisterContaining>);

impl RegistersContaining {
    pub(crate) fn from_words(words: Vec<RegisterContaining>) -> RegistersContaining {
        assert!(!words.is_empty());
        Self(words)
    }

    pub(crate) fn words(&self) -> &[RegisterContaining] {
        &self.0
    }

    pub(crate) fn words_mut(&mut self) -> impl Iterator<Item = &mut RegisterContaining> {
        self.0.iter_mut()
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + use<'_> {
        self.0
            .iter()
            .flat_map(move |rc| rc.symbol_uses(block_id, block_offset))
    }
}

impl Spanned for RegistersContaining {
    fn span(&self) -> Span {
        use chumsky::span::Span;
        let mut it = self.0.iter();
        match it.next() {
            Some(rc) => it.fold(rc.span(), |acc, rc| acc.union(rc.span())),
            None => {
                unreachable!("invariant broken: RegistersContaining contains no RegisterContaining instances")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RegisterContaining {
    Unallocated(Box<TaggedProgramInstruction>),
    Allocated(Address, Box<TaggedProgramInstruction>),
}

impl From<TaggedProgramInstruction> for RegisterContaining {
    fn from(inst: TaggedProgramInstruction) -> Self {
        RegisterContaining::Unallocated(Box::new(inst))
    }
}

impl Spanned for RegisterContaining {
    fn span(&self) -> Span {
        match self {
            RegisterContaining::Unallocated(b) | RegisterContaining::Allocated(_, b) => b.span(),
        }
    }
}

impl RegisterContaining {
    pub(crate) fn instruction(&self) -> &TaggedProgramInstruction {
        match self {
            RegisterContaining::Unallocated(tpi) => tpi,
            RegisterContaining::Allocated(_, tpi) => tpi,
        }
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + use<'_> {
        let mut result = Vec::new();
        for symbol_use in self.instruction().symbol_uses(block_id, block_offset) {
            let (name, span, symbol_definition) = symbol_use;
            match symbol_definition {
                def @ SymbolUse::Reference(_) => {
                    result.push((name, span, def));
                }
                SymbolUse::Definition(SymbolDefinition::Tag { .. }) => {
                    // Here we have a tag definition inside an
                    // RC-word.  Therefore the passed-in value of
                    // `block_id` is wrong (it refers to the block
                    // containing the RC-word, not to the RC-block)
                    // and the offset is similarly wrong.
                    //
                    // Therefore we will process these uses of symbols
                    // at the time we allocate addresses for RC-block
                    // words.
                }
                SymbolUse::Origin(_name, _block) => {
                    unreachable!("Found origin {name} inside an RC-word; the parser should have rejected this.");
                }
                SymbolUse::Definition(_) => {
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
        result.into_iter()
    }
}

/// Eventually we will support real expressions, but for now we only
/// suport literals and references to symbols ("equalities" in the
/// User Handbook).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Atom {
    SymbolOrLiteral(SymbolOrLiteral),
    Parens(Span, Script, Box<ArithmeticExpression>),
    RcRef(Span, RegistersContaining),
}

impl From<(Span, Script, SymbolName)> for Atom {
    fn from((span, script, name): (Span, Script, SymbolName)) -> Self {
        Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(script, name, span))
    }
}

impl From<SymbolOrLiteral> for Atom {
    fn from(value: SymbolOrLiteral) -> Self {
        Atom::SymbolOrLiteral(value)
    }
}

impl Atom {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(script, name, span)) => {
                result.push((
                    name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                ));
            }
            Atom::SymbolOrLiteral(SymbolOrLiteral::Literal(_) | SymbolOrLiteral::Here(_, _)) => (),
            Atom::Parens(_span, _script, expr) => {
                result.extend(expr.symbol_uses(block_id, block_offset));
            }
            Atom::RcRef(_span, rc_words) => {
                result.extend(rc_words.symbol_uses(block_id, block_offset));
            }
        }
        result.into_iter()
    }
}

impl Spanned for Atom {
    fn span(&self) -> Span {
        match self {
            Atom::SymbolOrLiteral(value) => value.span(),
            Atom::Parens(span, _script, _bae) => *span,
            Atom::RcRef(span, _) => *span,
        }
    }
}

impl From<LiteralValue> for Atom {
    fn from(literal: LiteralValue) -> Atom {
        Atom::SymbolOrLiteral(SymbolOrLiteral::Literal(literal))
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
            Atom::SymbolOrLiteral(value) => write!(f, "{value}"),
            Atom::Parens(_span, script, expr) => elevated_string(&expr.to_string(), script).fmt(f),
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
    Here(Script, Span),
}

impl SymbolOrLiteral {
    fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::with_capacity(1);
        match self {
            SymbolOrLiteral::Here(_, _) | SymbolOrLiteral::Literal(_) => (),
            SymbolOrLiteral::Symbol(script, name, span) => {
                let context: SymbolContext = (script, *span).into();
                let sym_use: SymbolUse = SymbolUse::Reference(context);
                result.push((name.clone(), *span, sym_use));
            }
        }
        result.into_iter()
    }
}

impl Spanned for SymbolOrLiteral {
    fn span(&self) -> Span {
        match self {
            SymbolOrLiteral::Symbol(_, _, span) => *span,
            SymbolOrLiteral::Literal(literal_value) => literal_value.span,
            SymbolOrLiteral::Here(_, span) => *span,
        }
    }
}

impl Display for SymbolOrLiteral {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolOrLiteral::Here(script, _span) => match script {
                Script::Super => f.write_str("@super_hash@"),
                Script::Normal => f.write_char('#'),
                Script::Sub => f.write_str("@sub_hash@"),
            },
            SymbolOrLiteral::Symbol(script, name, _) => {
                elevated_string(&name.to_string(), script).fmt(f)
            }
            SymbolOrLiteral::Literal(value) => value.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct SpannedSymbolOrLiteral {
    pub(crate) item: SymbolOrLiteral,
    pub(crate) span: Span,
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
    DeferredAddressing(Span),
    /// A configuration syllable (specified either in superscript or with a ‖).
    Config(ConfigValue),
    /// Described in section 6-2.8 "SPECIAL SYMBOLS" of the Users Handbook.
    PipeConstruct {
        index: SpannedSymbolOrLiteral,
        rc_word_span: Span,
        rc_word_value: RegisterContaining,
    },
    Null(Span),
}

impl Spanned for InstructionFragment {
    fn span(&self) -> Span {
        match self {
            InstructionFragment::Arithmetic(arithmetic_expression) => arithmetic_expression.span(),
            InstructionFragment::DeferredAddressing(span) => *span,
            InstructionFragment::Config(config_value) => config_value.span(),
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span,
                rc_word_value: _,
            } => {
                let start = index.span.start;
                let end = rc_word_span.end;
                span(start..end)
            }
            InstructionFragment::Null(span) => *span,
        }
    }
}

impl InstructionFragment {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<_> = Vec::new();
        match self {
            InstructionFragment::Null(_) => (),
            InstructionFragment::Arithmetic(expr) => {
                result.extend(expr.symbol_uses(block_id, block_offset));
            }
            InstructionFragment::DeferredAddressing(_) => (),
            InstructionFragment::Config(value) => {
                result.extend(value.symbol_uses(block_id, block_offset));
            }
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span: _,
                rc_word_value,
            } => {
                result.extend(
                    index
                        .item
                        .symbol_uses()
                        .map(|(name, span, mut symbol_use)| {
                            if let SymbolUse::Reference(context) = &mut symbol_use {
                                assert!(!context.is_address());
                                context.also_set_index();
                            };
                            (name, span, symbol_use)
                        }),
                );
                result.extend(rc_word_value.symbol_uses(block_id, block_offset));
            }
        }
        result.into_iter()
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
}

impl Spanned for Origin {
    fn span(&self) -> Span {
        match self {
            Origin::Literal(span, _) | Origin::Symbolic(span, _) => *span,
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
    fn symbol_uses(
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

impl Spanned for Commas {
    fn span(&self) -> Span {
        match &self {
            Commas::One(span) | Commas::Two(span) | Commas::Three(span) => *span,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct FragmentWithHold {
    pub(super) span: Span,
    pub(super) holdbit: HoldBit,
    pub(super) fragment: InstructionFragment,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CommasOrInstruction {
    I(FragmentWithHold),
    C(Option<Commas>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CommaDelimitedFragment {
    pub(crate) span: Span,
    pub(crate) leading_commas: Option<Commas>,
    pub(crate) holdbit: HoldBit,
    pub(crate) fragment: InstructionFragment,
    pub(crate) trailing_commas: Option<Commas>,
}

impl CommaDelimitedFragment {
    pub(crate) fn new(
        leading_commas: Option<Commas>,
        instruction: FragmentWithHold,
        trailing_commas: Option<Commas>,
    ) -> Self {
        let span: Span = {
            let spans: [Option<Span>; 3] = [
                leading_commas.as_ref().map(|c| c.span()),
                Some(instruction.span),
                trailing_commas.as_ref().map(|c| c.span()),
            ];
            match spans {
                [_, None, _] => {
                    unreachable!("CommaDelimitedInstruction cannot be completely empty")
                }
                [None, Some(m), None] => m,
                [None, Some(m), Some(r)] => span(m.start..r.end),
                [Some(l), _, Some(r)] => span(l.start..r.end),
                [Some(l), Some(m), None] => span(l.start..m.end),
            }
        };
        Self {
            span,
            leading_commas,
            holdbit: instruction.holdbit,
            fragment: instruction.fragment,
            trailing_commas,
        }
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        self.fragment.symbol_uses(block_id, block_offset)
    }
}

impl Spanned for CommaDelimitedFragment {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UntaggedProgramInstruction {
    pub(crate) fragments: Vec<CommaDelimitedFragment>,
}

impl From<Vec<CommaDelimitedFragment>> for UntaggedProgramInstruction {
    fn from(fragments: Vec<CommaDelimitedFragment>) -> Self {
        assert!(!fragments.is_empty(), "input fragments should not be empty");
        Self { fragments }
    }
}

impl UntaggedProgramInstruction {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + use<'_> {
        self.fragments
            .iter()
            .flat_map(move |fragment| fragment.symbol_uses(block_id, offset))
    }
}

impl Spanned for UntaggedProgramInstruction {
    fn span(&self) -> Span {
        match (self.fragments.first(), self.fragments.last()) {
            (Some(f), Some(b)) => span(f.span.start..b.span.end),
            (None, _) | (_, None) => {
                unreachable!("invariant broken: zero fragments in UntaggedProgramInstruction");
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct EqualityValue {
    pub(super) span: Span,
    pub(super) inner: UntaggedProgramInstruction,
}

impl Spanned for EqualityValue {
    fn span(&self) -> Span {
        self.span
    }
}

impl From<(Span, UntaggedProgramInstruction)> for EqualityValue {
    fn from((span, inner): (Span, UntaggedProgramInstruction)) -> Self {
        Self { span, inner }
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
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        [(
            self.name.clone(),
            self.span,
            SymbolUse::Definition(SymbolDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span: self.span,
            })),
        )]
        .into_iter()
    }
}

impl PartialOrd for Tag {
    /// Ordering for tags ignores the span.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Tag {
    /// Ordering for tags ignores the span.
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(&other.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TaggedProgramInstruction {
    pub(crate) span: Span,
    pub(crate) tags: Vec<Tag>,
    pub(crate) instruction: UntaggedProgramInstruction,
}

impl TaggedProgramInstruction {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result = Vec::new();
        result.extend(
            self.tags
                .iter()
                .flat_map(|tag| tag.symbol_uses(block_id, offset)),
        );
        result.extend(self.instruction.symbol_uses(block_id, offset));
        result.into_iter()
    }

    #[cfg(test)]
    pub(crate) fn single(
        tags: Vec<Tag>,
        holdbit: HoldBit,
        inst_span: Span,
        frag_span: Span,
        frag: InstructionFragment,
    ) -> TaggedProgramInstruction {
        TaggedProgramInstruction::multiple(
            tags,
            inst_span,
            vec![CommaDelimitedFragment {
                span: frag_span,
                leading_commas: None,
                holdbit,
                fragment: frag,
                trailing_commas: None,
            }],
        )
    }

    #[cfg(test)]
    pub(crate) fn multiple(
        tags: Vec<Tag>,
        span: Span,
        fragments: Vec<CommaDelimitedFragment>,
    ) -> TaggedProgramInstruction {
        assert!(!fragments.is_empty());
        TaggedProgramInstruction {
            tags,
            span,
            instruction: UntaggedProgramInstruction::from(fragments),
        }
    }

    #[inline(always)]
    fn emitted_word_count(&self) -> Unsigned18Bit {
        Unsigned18Bit::ONE
    }
}

impl Spanned for TaggedProgramInstruction {
    fn span(&self) -> Span {
        let begin = match self.tags.first() {
            Some(t) => t.span.start,
            None => self.instruction.span().start,
        };
        let end = self.instruction.span().end;
        Span::from(begin..end)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InstructionSequence {
    instructions: Vec<TaggedProgramInstruction>,
}

impl chumsky::container::Container<TaggedProgramInstruction> for InstructionSequence {
    fn push(&mut self, item: TaggedProgramInstruction) {
        self.instructions.push(item)
    }

    fn with_capacity(n: usize) -> Self {
        InstructionSequence {
            instructions: Vec::with_capacity(n),
        }
    }
}

impl From<Vec<TaggedProgramInstruction>> for InstructionSequence {
    fn from(v: Vec<TaggedProgramInstruction>) -> Self {
        InstructionSequence { instructions: v }
    }
}

impl FromIterator<TaggedProgramInstruction> for InstructionSequence {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = TaggedProgramInstruction>,
    {
        Self {
            instructions: iter.into_iter().collect(),
        }
    }
}

impl InstructionSequence {
    pub(super) fn iter(&self) -> impl Iterator<Item = &TaggedProgramInstruction> {
        self.instructions.iter()
    }

    pub(crate) fn first(&self) -> Option<&TaggedProgramInstruction> {
        self.instructions.first()
    }

    #[cfg(test)]
    pub(crate) fn as_slice(&self) -> &[TaggedProgramInstruction] {
        self.instructions.as_slice()
    }

    pub(super) fn assign_rc_words<R: RcAllocator>(
        &mut self,
        symtab: &mut SymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for ref mut statement in self.instructions.iter_mut() {
            statement.assign_rc_words(symtab, rc_allocator)?;
        }
        Ok(())
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::new();
        for (offset, statement) in self.instructions.iter().enumerate() {
            let off: Unsigned18Bit = Unsigned18Bit::try_from(offset)
                .expect("block should not be larger than the TX-2's memory");
            result.extend(statement.symbol_uses(block_id, off));
        }
        result.into_iter()
    }

    pub(crate) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.instructions
            .iter()
            .map(|st| st.emitted_word_count())
            .sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    pub(crate) blocks: Vec<ManuscriptBlock>,
    pub(crate) equalities: Vec<Equality>,
    pub(crate) macros: BTreeMap<SymbolName, MacroDefinition>,
}

impl SourceFile {
    fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> + '_ {
        fn offset_to_block_id<T>((offset, item): (usize, T)) -> (BlockIdentifier, T) {
            (BlockIdentifier::from(offset), item)
        }

        let uses_in_instructions = self
            .blocks
            .iter()
            .enumerate()
            .map(offset_to_block_id)
            .flat_map(|(block_id, block)| block.symbol_uses(block_id));
        let uses_in_assignments = self.equalities.iter().flat_map(|eq| eq.symbol_uses());
        uses_in_instructions.chain(uses_in_assignments)
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
    BaseChange(NumeralMode),
    Punch(PunchCommand),
    Macro(MacroDefinition),
}

// The RHS of an assignment can be "any 36-bit value" (see TX-2
// Users Handbook, section 6-2.2, page 156 = 6-6).  Hence if the
// RHS of the assignment is symbolic the user needs to be able to
// set the hold bit with "h".  However, since we don't allow tags
// on the RHS, the value cannot be a TaggedProgramInstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Equality {
    pub(crate) span: Span,
    pub(crate) name: SymbolName,
    pub(crate) value: EqualityValue,
}

impl Equality {
    fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        [(
            self.name.clone(),
            self.span,
            SymbolUse::Definition(
                // TODO: the expression.clone() on the next line is expensive.
                SymbolDefinition::Equality(self.value.clone()),
            ),
        )]
        .into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptLine {
    Meta(ManuscriptMetaCommand),
    Eq(Equality),
    OriginOnly(Origin),
    TagsOnly(Vec<Tag>),
    StatementOnly(TaggedProgramInstruction),
    OriginAndStatement(Origin, TaggedProgramInstruction),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroParameter {
    pub(crate) name: SymbolName,
    pub(crate) span: Span,
    pub(crate) preceding_terminator: Token,
}

/// As defined with ☛☛DEF, a macro's name is followed by a terminator,
/// or by a terminator and some arguments.  We model each argument as
/// being introduced by its preceding terminator.  If there are no
/// arguments, MacroArguments::Zero(token) represents that uses of the
/// macro's name are followed by the indicated token (which terminates
/// the macro name, not a dummy parameter).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MacroDummyParameters {
    Zero(Token),
    OneOrMore(Vec<MacroParameter>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroDefinition {
    pub(crate) name: SymbolName, // composite character macros are not yet supported
    pub(crate) params: MacroDummyParameters,
    // body should probably be a sequence of ManuscriptLine in order
    // to allow an origin specification to exist within a macro body.
    // But that is not supported yet.
    pub(crate) body: InstructionSequence,
    pub(crate) span: Span,
}

#[cfg(test)] // not yet used outside tests.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroInvocation {
    pub(crate) macro_def: MacroDefinition,
    pub(crate) param_values: BTreeMap<SymbolName, Option<ArithmeticExpression>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ManuscriptBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) statements: InstructionSequence,
}

impl ManuscriptBlock {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = (SymbolName, Span, SymbolUse)> {
        let mut result: Vec<(SymbolName, Span, SymbolUse)> = Vec::new();
        if let Some(origin) = self.origin.as_ref() {
            result.extend(origin.symbol_uses(block_id));
        }
        result.extend(self.statements.symbol_uses(block_id));
        result.into_iter()
    }

    pub(crate) fn instruction_count(&self) -> Unsigned18Bit {
        self.statements.emitted_word_count()
    }

    pub(crate) fn origin_span(&self) -> Span {
        if let Some(origin) = self.origin.as_ref() {
            origin.span()
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
    pub(crate) blocks: BTreeMap<BlockIdentifier, (Option<Origin>, LocatedBlock)>,
    pub(crate) equalities: Vec<Equality>,
    pub(crate) entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn new(
        blocks: BTreeMap<BlockIdentifier, (Option<Origin>, LocatedBlock)>,
        equalities: Vec<Equality>,
        entry_point: Option<Address>,
    ) -> Self {
        Self {
            blocks,
            equalities,
            entry_point,
        }
    }

    pub(crate) fn position_rc_block(&mut self) -> Address {
        self.blocks
            .values()
            .map(|(_origin, block)| block.following_addr())
            .max()
            .unwrap_or_else(Origin::default_address)
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedBlock {
    pub(crate) location: Address,
    pub(crate) statements: InstructionSequence,
}

impl LocatedBlock {
    pub(crate) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.statements.emitted_word_count()
    }

    pub(crate) fn following_addr(&self) -> Address {
        self.location.index_by(self.emitted_word_count())
    }
}
