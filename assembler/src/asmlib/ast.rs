//! Abstract syntax representation.   It's mostly not actually a tree.
//!
//! In the AST, terminology follows the TX-2 assembler's
//! documentation, and this doesn't always match modern usage.  In
//! particular, "block" is used to refer to a contiguously-allocated
//! sequence of instructions which share an origin statement.  Such as
//! the RC-block.  This is not the same as a block in a language like
//! C, where "block" is also a declaration-scoping construct.
//!
//! Instead, in the TX-2 assembler, scopes are introduced by macro
//! expansion.  So, a "block" may contain some instructions followed
//! by a macro-expansion (which has an associated scope) which itself
//! might contain a macro-expansion, with another scope.
use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use super::collections::OneOrMore;
use super::glyph;
use super::lexer::Token;
use super::span::*;
use super::state::NumeralMode;
use super::symbol::{InconsistentSymbolUse, SymbolContext, SymbolName};
use super::symtab::{
    BadSymbolDefinition, ExplicitDefinition, ExplicitSymbolTable, ImplicitSymbolTable,
    TagDefinition,
};
use super::types::*;

#[derive(Debug, PartialEq, Eq, Clone)]
enum SymbolUse {
    Reference(SymbolContext),
    Definition(ExplicitDefinition),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum RcWordAllocationFailure {
    RcBlockTooBig {
        source: RcWordSource,
        rc_block_len: usize,
    },
    InconsistentTag {
        tag_name: SymbolName,
        span: Span,
        existing: Box<ExplicitDefinition>,
        proposed: Box<TagDefinition>,
    },
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
            RcWordAllocationFailure::InconsistentTag {
                tag_name,
                span: _,
                existing,
                proposed,
            } => {
                write!(
                    f,
                    "failed to define tag {tag_name} because it already had a previous definition: {existing} versus {proposed}"
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        self.magnitude.symbol_uses(block_id, block_offset)
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<SignedAtom> {
        self.magnitude
            .substitute_macro_parameters(param_values, on_missing, macros)
            .map(|magnitude| SignedAtom {
                magnitude,
                ..self.clone()
            })
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
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

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<ArithmeticExpression> {
        match self
            .first
            .substitute_macro_parameters(param_values, on_missing, macros)
        {
            None => None,
            Some(first) => {
                let mut tail: Vec<(Operator, SignedAtom)> = Vec::with_capacity(self.tail.len());
                for (op, atom) in self.tail.iter() {
                    match atom.substitute_macro_parameters(param_values, on_missing, macros) {
                        Some(atom) => {
                            tail.push((*op, atom));
                        }
                        None => {
                            return None;
                        }
                    }
                }
                Some(ArithmeticExpression { first, tail })
            }
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        self.expr
            .symbol_uses(block_id, block_offset)
            .map(|r| match r {
                Ok((name, span, _ignore_symbol_use)) => Ok((
                    name,
                    span,
                    SymbolUse::Reference(SymbolContext::configuration(span)),
                )),
                Err(e) => Err(e),
            })
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<ConfigValue> {
        self.expr
            .substitute_macro_parameters(param_values, on_missing, macros)
            .map(|expr| ConfigValue {
                expr,
                already_superscript: self.already_superscript,
            })
    }
}

impl Spanned for ConfigValue {
    fn span(&self) -> Span {
        self.expr.span()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RegistersContaining(OneOrMore<RegisterContaining>);

impl RegistersContaining {
    pub(crate) fn from_words(words: OneOrMore<RegisterContaining>) -> RegistersContaining {
        Self(words)
    }

    pub(crate) fn words(&self) -> impl Iterator<Item = &RegisterContaining> {
        self.0.iter()
    }

    pub(crate) fn words_mut(&mut self) -> impl Iterator<Item = &mut RegisterContaining> {
        self.0.iter_mut()
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        block_offset: Unsigned18Bit,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + use<'_>
    {
        self.0
            .iter()
            .flat_map(move |rc| rc.symbol_uses(block_id, block_offset))
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<RegistersContaining> {
        // TODO: this implementation probably requires more thought.
        // At the moment, if the contents of {...} yield any single
        // item that gets omitted because it references an unbound
        // macro paramter, then the whole {...} (and therefore
        // anything containing it) gets omitted.
        //
        // This may not match the required behaviour of the TX-2's M4
        // assembler, which might instead just omit that RC-word.
        // However, if we switch to that option, then this could
        // create a situation in which {...} results in zero words of
        // the RC-block being reserved.  In that case, what is the
        // resulting numerical value of the {...} expression?  If it
        // actually does reserve zero words, then it means that two or
        // more instances of {...} could resolve to the same address,
        // and that is likely not intended.  It wold also mean trouble
        // for the current implementation of the Spanned trait for
        // RegistersContaining.
        let tmp_rc: OneOrMore<Option<RegisterContaining>> = self
            .0
            .map(|rc| rc.substitute_macro_parameters(param_values, on_missing, macros));
        if tmp_rc.iter().all(|maybe_rc| maybe_rc.is_some()) {
            Some(RegistersContaining(tmp_rc.into_map(|maybe_rc| {
                maybe_rc.expect("we already checked this wasn't None")
            })))
        } else {
            None
        }
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + use<'_>
    {
        let mut result: Vec<Result<_, _>> = Vec::new();
        for r in self.instruction().symbol_uses(block_id, block_offset) {
            match r {
                Ok((name, span, symbol_definition)) => {
                    match symbol_definition {
                        def @ SymbolUse::Reference(_) => {
                            result.push(Ok((name, span, def)));
                        }
                        SymbolUse::Definition(ExplicitDefinition::Tag { .. }) => {
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
                        SymbolUse::Definition(ExplicitDefinition::Origin(_, _)) => {
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
                Err(e) => {
                    result.push(Err(e));
                }
            }
        }
        result.into_iter()
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<RegisterContaining> {
        match self {
            RegisterContaining::Unallocated(tagged_program_instruction) => {
                tagged_program_instruction
                    .substitute_macro_parameters(param_values, on_missing, macros)
                    .map(|tagged_program_instruction| {
                        RegisterContaining::Unallocated(Box::new(tagged_program_instruction))
                    })
            }
            RegisterContaining::Allocated(_address, _tagged_program_instruction) => {
                // One reason we don't support this is because if we
                // twice instantiate a macro which contains {...} or a
                // pipe construct, then both of those RC-words would
                // have the same address, and this is likely not
                // intended.  It's certainly user-surprising.
                //
                // The second reason we don't support this (and the
                // reason why we don't need to issue an error message
                // for the user) is that the assembler implementation
                // does in fact perform macro-expansion before
                // RC-words are allocated.
                unreachable!(
                    "macro expansion must be completed before any RC-block addresses are allocated"
                )
            }
        }
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut result: Vec<Result<_, _>> = Vec::with_capacity(1);
        match self {
            Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(script, name, span)) => {
                result.push(Ok((
                    name.clone(),
                    *span,
                    SymbolUse::Reference(SymbolContext::from((script, *span))),
                )));
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

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<Atom> {
        match self {
            Atom::SymbolOrLiteral(symbol_or_literal) => {
                match symbol_or_literal.substitute_macro_parameters(param_values, on_missing) {
                    SymbolSubstitution::AsIs(symbol_or_literal) => {
                        Some(Atom::SymbolOrLiteral(symbol_or_literal))
                    }
                    SymbolSubstitution::Hit(span, script, arithmetic_expression) => Some(
                        Atom::Parens(span, script, Box::new(arithmetic_expression.clone())),
                    ),
                    SymbolSubstitution::Omit => {
                        // The parameter was not set, and this atom is
                        // being used in a context where omitted
                        // parameters cause the affected instructin to
                        // be omitted.  That is, this expression is
                        // not on the right-hand-side of an equality.
                        None
                    }
                    SymbolSubstitution::Zero(span) => {
                        Some(Atom::SymbolOrLiteral(SymbolOrLiteral::Literal(
                            LiteralValue {
                                span,
                                // Since the value is zero the elevation actually doesn't matter.
                                elevation: Script::Normal,
                                value: Unsigned36Bit::ZERO,
                            },
                        )))
                    }
                }
            }
            Atom::Parens(span, script, arithmetic_expression) => arithmetic_expression
                .substitute_macro_parameters(param_values, on_missing, macros)
                .map(|arithmetic_expression| {
                    Atom::Parens(*span, *script, Box::new(arithmetic_expression))
                }),
            Atom::RcRef(span, registers_containing) => registers_containing
                .substitute_macro_parameters(param_values, on_missing, macros)
                .map(|registers_containing| Atom::RcRef(*span, registers_containing)),
        }
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
pub(crate) enum SymbolSubstitution<T> {
    AsIs(T),
    Hit(Span, Script, ArithmeticExpression),
    Omit,
    Zero(Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SymbolOrLiteral {
    Symbol(Script, SymbolName, Span),
    Literal(LiteralValue),
    Here(Script, Span),
}

impl SymbolOrLiteral {
    fn symbol_uses(
        &self,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut result = Vec::with_capacity(1);
        match self {
            SymbolOrLiteral::Here(_, _) | SymbolOrLiteral::Literal(_) => (),
            SymbolOrLiteral::Symbol(script, name, span) => {
                let context: SymbolContext = (script, *span).into();
                let sym_use: SymbolUse = SymbolUse::Reference(context);
                result.push(Ok((name.clone(), *span, sym_use)));
            }
        }
        result.into_iter()
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
    ) -> SymbolSubstitution<SymbolOrLiteral> {
        match self {
            SymbolOrLiteral::Symbol(_script, symbol_name, _span) => {
                match param_values.get(symbol_name) {
                    Some((
                        span,
                        Some(MacroParameterValue::Value(script, arithmetic_expression)),
                    )) => {
                        // symbol_name was a parameter name, and the
                        // macro invocation specified it, so
                        // substitute it.
                        SymbolSubstitution::Hit(*span, *script, arithmetic_expression.clone())
                    }
                    Some((span, None)) => {
                        // symbol_name was a parameter name, but the
                        // macro invocation did not specify it, so we
                        // either elide the instruction or behave if
                        // it is zero, according to on_missing.
                        match on_missing {
                            OnUnboundMacroParameter::ElideReference => SymbolSubstitution::Omit,
                            OnUnboundMacroParameter::SubstituteZero => {
                                SymbolSubstitution::Zero(*span)
                            }
                        }
                    }
                    None => {
                        // symbol_name is not a macro parameter.
                        SymbolSubstitution::AsIs(self.clone())
                    }
                }
            }
            SymbolOrLiteral::Literal(literal) => {
                SymbolSubstitution::AsIs(SymbolOrLiteral::Literal(literal.clone()))
            }
            SymbolOrLiteral::Here(script, span) => {
                SymbolSubstitution::AsIs(SymbolOrLiteral::Here(*script, *span))
            }
        }
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

impl SpannedSymbolOrLiteral {
    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
    ) -> SymbolSubstitution<SpannedSymbolOrLiteral> {
        match self
            .item
            .substitute_macro_parameters(param_values, on_missing)
        {
            SymbolSubstitution::AsIs(item) => SymbolSubstitution::AsIs(SpannedSymbolOrLiteral {
                item,
                span: self.span,
            }),
            SymbolSubstitution::Hit(span, script, arithmetic_expression) => {
                SymbolSubstitution::Hit(span, script, arithmetic_expression)
            }
            SymbolSubstitution::Omit => SymbolSubstitution::Omit,
            SymbolSubstitution::Zero(span) => SymbolSubstitution::Zero(span),
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut uses: Vec<Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> =
            Vec::new();
        match self {
            InstructionFragment::Null(_) => (),
            InstructionFragment::Arithmetic(expr) => {
                uses.extend(expr.symbol_uses(block_id, block_offset));
            }
            InstructionFragment::DeferredAddressing(_) => (),
            InstructionFragment::Config(value) => {
                uses.extend(value.symbol_uses(block_id, block_offset));
            }
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span: _,
                rc_word_value,
            } => {
                for r in index.item.symbol_uses() {
                    match r {
                        Ok((name, span, mut symbol_use)) => {
                            if let SymbolUse::Reference(context) = &mut symbol_use {
                                assert!(!context.is_address());
                                if let Err(e) = context.also_set_index(&name, span) {
                                    uses.push(Err(e));
                                } else {
                                    uses.push(Ok((name, span, symbol_use)));
                                }
                            } else {
                                uses.push(Ok((name, span, symbol_use)));
                            }
                        }
                        Err(e) => {
                            uses.push(Err(e));
                        }
                    }
                }
                uses.extend(rc_word_value.symbol_uses(block_id, block_offset));
            }
        }
        uses.into_iter()
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<InstructionFragment> {
        match self {
            InstructionFragment::Arithmetic(arithmetic_expression) => arithmetic_expression
                .substitute_macro_parameters(param_values, on_missing, macros)
                .map(InstructionFragment::Arithmetic),
            InstructionFragment::DeferredAddressing(span) => {
                Some(InstructionFragment::DeferredAddressing(*span))
            }
            InstructionFragment::Config(config_value) => config_value
                .substitute_macro_parameters(param_values, on_missing, macros)
                .map(InstructionFragment::Config),
            InstructionFragment::PipeConstruct {
                index,
                rc_word_span,
                rc_word_value,
            } => match index.substitute_macro_parameters(param_values, on_missing) {
                SymbolSubstitution::AsIs(index) => rc_word_value
                    .substitute_macro_parameters(param_values, on_missing, macros)
                    .map(|rc_word_value| InstructionFragment::PipeConstruct {
                        index,
                        rc_word_span: *rc_word_span,
                        rc_word_value,
                    }),
                SymbolSubstitution::Hit(_span, _script, _arithmetic_expression) => {
                    todo!("macro parameter expansion is not yet fully supported in the index part of pipe constructs")
                }
                SymbolSubstitution::Omit => None,
                SymbolSubstitution::Zero(span) => Some(InstructionFragment::Null(span)),
            },
            InstructionFragment::Null(span) => Some(InstructionFragment::Null(*span)),
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

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub(crate) enum Origin {
    /// An origin specified directly as a number.
    Literal(Span, Address),
    /// An origin specified by name (which would refer to e.g. an
    /// equality).
    Symbolic(Span, SymbolName),
    /// An origin which was intiially symbolic only, but whose location we deduced.
    Deduced(Span, SymbolName, Address),
}

impl Display for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Origin::Literal(_span, addr) => fmt::Display::fmt(&addr, f),
            Origin::Symbolic(_span, sym) => fmt::Display::fmt(&sym, f),
            Origin::Deduced(_span, name, addr) => {
                write!(f, "{name} (deduced to be at address {addr:o})")
            }
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
            Origin::Deduced(span, _, _) | Origin::Literal(span, _) | Origin::Symbolic(span, _) => {
                *span
            }
        }
    }
}

impl Octal for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Deduced(_span, name, address) => {
                write!(f, "{name} (deduced to be at {address:o})")
            }
            Origin::Literal(_span, address) => fmt::Octal::fmt(&address, f),
            Origin::Symbolic(_span, name) => fmt::Display::fmt(&name, f),
        }
    }
}

impl Origin {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut result = Vec::with_capacity(1);
        match self {
            Origin::Literal(_span, _) => (),
            org @ Origin::Deduced(span, name, _) => {
                // We won't have any deduced origin values at this
                // time the symbol uses are enumerate, but this case
                // is just here for completeness.
                result.push(Ok((
                    name.clone(),
                    *span,
                    SymbolUse::Definition(ExplicitDefinition::Origin(org.clone(), block_id)),
                )));
            }
            org @ Origin::Symbolic(span, name) => {
                result.push(Ok((
                    name.clone(),
                    *span,
                    SymbolUse::Definition(ExplicitDefinition::Origin(org.clone(), block_id)),
                )));
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + '_
    {
        self.fragment.symbol_uses(block_id, block_offset)
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<CommaDelimitedFragment> {
        self.fragment
            .substitute_macro_parameters(param_values, on_missing, macros)
            .map(|fragment| Self {
                fragment,
                ..self.clone()
            })
    }
}

impl Spanned for CommaDelimitedFragment {
    fn span(&self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UntaggedProgramInstruction {
    pub(crate) fragments: OneOrMore<CommaDelimitedFragment>,
}

impl From<OneOrMore<CommaDelimitedFragment>> for UntaggedProgramInstruction {
    fn from(fragments: OneOrMore<CommaDelimitedFragment>) -> Self {
        Self { fragments }
    }
}

impl UntaggedProgramInstruction {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
        offset: Unsigned18Bit,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + use<'_>
    {
        self.fragments
            .iter()
            .flat_map(move |fragment| fragment.symbol_uses(block_id, offset))
    }
}

impl UntaggedProgramInstruction {
    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<UntaggedProgramInstruction> {
        let tmp_frags: OneOrMore<Option<CommaDelimitedFragment>> = self
            .fragments
            .map(|frag| frag.substitute_macro_parameters(param_values, on_missing, macros));
        if tmp_frags.iter().any(|frag| frag.is_none()) {
            None
        } else {
            Some(UntaggedProgramInstruction {
                fragments: tmp_frags.into_map(|mut maybe_frag| {
                    maybe_frag
                        .take()
                        .expect("we already checked this fragment wasn't None")
                }),
            })
        }
    }
}

impl Spanned for UntaggedProgramInstruction {
    fn span(&self) -> Span {
        span(self.fragments.first().span.start..self.fragments.last().span.end)
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

impl EqualityValue {
    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> EqualityValue {
        // If we set an equality to the value of an unspecified macro
        // parameter, then that equality is set to zero.  This is
        // required by item (7) of section 6-4.6 ("The Defining
        // Subprogram") of the TX-2 User's Handbook.
        //
        // However, that item does not cover more complex cases like
        // "G = DUM2 + 4".  Our current interpretation will assign G
        // the value 4 when DUM2 is an unspecified macro parameter.
        // However, analysis of actual TX-2 programs may show that
        // this is not the correct interpretation.
        if let Some(inner) = self.inner.substitute_macro_parameters(
            param_values,
            // We use SubstituteZero here for the reasons
            // described in the block comment above.
            OnUnboundMacroParameter::SubstituteZero,
            macros,
        ) {
            EqualityValue {
                span: self.span,
                inner,
            }
        } else {
            unreachable!(
                "substitute_macro_parameters should not return None when OnUnboundMacroParameter::SubstituteZero is in effect"
            )
        }
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        [Ok((
            self.name.clone(),
            self.span,
            SymbolUse::Definition(ExplicitDefinition::Tag(TagDefinition::Unresolved {
                block_id,
                block_offset,
                span: self.span,
            })),
        ))]
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
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut result: Vec<Result<_, _>> = Vec::new();
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
        TaggedProgramInstruction {
            tags,
            span: inst_span,
            instruction: UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                span: frag_span,
                leading_commas: None,
                holdbit,
                fragment: frag,
                trailing_commas: None,
            })),
        }
    }

    #[cfg(test)]
    pub(crate) fn multiple(
        tags: Vec<Tag>,
        span: Span,
        first_fragment: CommaDelimitedFragment,
        more_fragments: Vec<CommaDelimitedFragment>,
    ) -> TaggedProgramInstruction {
        TaggedProgramInstruction {
            tags,
            span,
            instruction: UntaggedProgramInstruction::from(OneOrMore::with_tail(
                first_fragment,
                more_fragments,
            )),
        }
    }

    #[inline(always)]
    fn emitted_word_count(&self) -> Unsigned18Bit {
        Unsigned18Bit::ONE
    }

    pub(super) fn substitute_macro_parameters(
        &self,
        param_values: &MacroParameterBindings,
        on_missing: OnUnboundMacroParameter,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> Option<TaggedProgramInstruction> {
        self.instruction
            .substitute_macro_parameters(param_values, on_missing, macros)
            .map(|instruction| TaggedProgramInstruction {
                span: self.span,
                tags: self.tags.clone(),
                instruction,
            })
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstructionSequence {
    pub(super) local_symbols: Option<ExplicitSymbolTable>,
    pub(super) instructions: Vec<TaggedProgramInstruction>,
}

#[cfg(test)]
impl From<Vec<TaggedProgramInstruction>> for InstructionSequence {
    fn from(v: Vec<TaggedProgramInstruction>) -> Self {
        InstructionSequence {
            local_symbols: None,
            instructions: v,
        }
    }
}

impl FromIterator<TaggedProgramInstruction> for InstructionSequence {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = TaggedProgramInstruction>,
    {
        InstructionSequence {
            local_symbols: None,
            instructions: iter.into_iter().collect(),
        }
    }
}

fn block_items_with_offset<T, I>(items: I) -> impl Iterator<Item = (Unsigned18Bit, T)>
where
    I: Iterator<Item = T>,
{
    items.enumerate().map(|(offset, item)| {
        let off: Unsigned18Bit = Unsigned18Bit::try_from(offset)
            .expect("block should not be larger than the TX-2's memory");
        (off, item)
    })
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) enum SymbolTableBuildFailure {
    InconsistentUsage(InconsistentSymbolUse),
    BadDefinition(BadSymbolDefinition),
}

impl Spanned for SymbolTableBuildFailure {
    fn span(&self) -> Span {
        match self {
            SymbolTableBuildFailure::InconsistentUsage(inconsistent_symbol_use) => {
                inconsistent_symbol_use.span()
            }
            SymbolTableBuildFailure::BadDefinition(bad_symbol_definition) => {
                bad_symbol_definition.span()
            }
        }
    }
}

impl Display for SymbolTableBuildFailure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SymbolTableBuildFailure::InconsistentUsage(inconsistent_symbol_use) => {
                write!(f, "{inconsistent_symbol_use}")
            }
            SymbolTableBuildFailure::BadDefinition(bad_symbol_definition) => {
                write!(f, "{bad_symbol_definition}")
            }
        }
    }
}

impl Error for SymbolTableBuildFailure {}

fn build_local_symbol_table<'a, I>(
    block_identifier: BlockIdentifier,
    instructions: I,
) -> Result<ExplicitSymbolTable, OneOrMore<SymbolTableBuildFailure>>
where
    I: Iterator<Item = &'a TaggedProgramInstruction>,
{
    let mut errors: Vec<SymbolTableBuildFailure> = Default::default();
    let mut local_symbols = ExplicitSymbolTable::default();
    for (offset, instruction) in block_items_with_offset(instructions) {
        for r in instruction
            .symbol_uses(block_identifier, offset)
            .filter_map(definitions_only)
        {
            match r {
                Ok((symbol_name, _span, definition)) => {
                    if let Err(e) = local_symbols.define(symbol_name.clone(), definition) {
                        errors.push(SymbolTableBuildFailure::BadDefinition(e));
                    }
                }
                Err(e) => {
                    errors.push(SymbolTableBuildFailure::InconsistentUsage(e));
                }
            }
        }
    }
    match OneOrMore::try_from_vec(errors) {
        Err(_) => Ok(local_symbols), // error vector is empty
        Ok(errors) => Err(errors),
    }
}

#[test]
fn test_build_local_symbol_table_happy_case() {
    let instruction_tagged_with = |name: &str, beginpos: usize| {
        let tag_span = span(beginpos..(beginpos + 1));
        let literal_span = span((beginpos + 3)..(beginpos + 4));
        TaggedProgramInstruction::single(
            vec![Tag {
                name: SymbolName::from(name),
                span: tag_span,
            }],
            HoldBit::Unspecified,
            literal_span,
            literal_span,
            InstructionFragment::from((literal_span, Script::Normal, Unsigned36Bit::ZERO)),
        )
    };

    let seq = InstructionSequence {
        local_symbols: Some(ExplicitSymbolTable::default()),
        instructions: vec![
            // Two lines which are identical (hence with the same tag)
            // apart from their spans.
            instruction_tagged_with("T", 0),
            instruction_tagged_with("U", 5),
        ],
    };

    let mut expected: ExplicitSymbolTable = ExplicitSymbolTable::default();
    expected
        .define(
            SymbolName::from("T"),
            ExplicitDefinition::Tag(TagDefinition::Unresolved {
                block_id: BlockIdentifier::from(0),
                block_offset: u18!(0),
                span: span(0..1),
            }),
        )
        .expect("symbol definition should be OK since there is no other defintion for that symbol");
    expected
        .define(
            SymbolName::from("U"),
            ExplicitDefinition::Tag(TagDefinition::Unresolved {
                block_id: BlockIdentifier::from(0),
                block_offset: u18!(1),
                span: span(5..6),
            }),
        )
        .expect("symbol definition should be OK since there is no other defintion for that symbol");
    assert_eq!(
        build_local_symbol_table(BlockIdentifier::from(0), seq.iter()),
        Ok(expected)
    );
}

#[test]
fn test_build_local_symbol_table_detects_tag_conflict() {
    let instruction_tagged_with_t = |beginpos: usize| {
        // This is the result of parsing a line "T->0\n" at some
        // position `beginpos`.
        let tag_span = span(beginpos..(beginpos + 1));
        let literal_span = span((beginpos + 3)..(beginpos + 4));
        TaggedProgramInstruction::single(
            vec![Tag {
                name: SymbolName::from("T"),
                span: tag_span,
            }],
            HoldBit::Unspecified,
            literal_span,
            literal_span,
            InstructionFragment::from((literal_span, Script::Normal, Unsigned36Bit::ZERO)),
        )
    };

    let seq = InstructionSequence {
        local_symbols: Some(ExplicitSymbolTable::default()),
        instructions: vec![
            // Two lines which are identical (hence with the same tag)
            // apart from their spans.
            instruction_tagged_with_t(0),
            instruction_tagged_with_t(5),
        ],
    };

    assert_eq!(
        build_local_symbol_table(BlockIdentifier::from(0), seq.iter()),
        Err(OneOrMore::new(SymbolTableBuildFailure::BadDefinition(
            BadSymbolDefinition {
                symbol_name: SymbolName::from("T"),
                span: span(5..6),
                existing: Box::new(ExplicitDefinition::Tag(TagDefinition::Unresolved {
                    block_id: BlockIdentifier::from(0),
                    block_offset: u18!(0),
                    span: span(0..1),
                })),
                proposed: Box::new(ExplicitDefinition::Tag(TagDefinition::Unresolved {
                    block_id: BlockIdentifier::from(0),
                    block_offset: u18!(1),
                    span: span(5..6),
                }))
            }
        )))
    );
}

impl InstructionSequence {
    pub(super) fn iter(&self) -> impl Iterator<Item = &TaggedProgramInstruction> {
        self.instructions.iter()
    }

    pub(crate) fn first(&self) -> Option<&TaggedProgramInstruction> {
        self.instructions.first()
    }

    pub(super) fn allocate_rc_words<R: RcAllocator>(
        &mut self,
        explicit_symtab: &mut ExplicitSymbolTable,
        implicit_symtab: &mut ImplicitSymbolTable,
        rc_allocator: &mut R,
    ) -> Result<(), RcWordAllocationFailure> {
        for ref mut statement in self.instructions.iter_mut() {
            statement.allocate_rc_words(explicit_symtab, implicit_symtab, rc_allocator)?;
        }
        Ok(())
    }

    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let no_symbols = ExplicitSymbolTable::default();
        let local_scope: &ExplicitSymbolTable = self.local_symbols.as_ref().unwrap_or(&no_symbols);
        let mut result: Vec<Result<_, _>> = Vec::new();

        for (off, statement) in block_items_with_offset(self.instructions.iter()) {
            result.extend(statement.symbol_uses(block_id, off).filter(|r| match r {
                Ok((symbol, _, _)) => !local_scope.is_defined(symbol),
                Err(_) => true,
            }));
        }
        result.into_iter()
    }

    pub(crate) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.iter().map(|st| st.emitted_word_count()).sum()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    /// Each block is an optional origin followed by some
    /// instructions.  A block is not a scoping artifact (see the
    /// module documentation).
    pub(crate) blocks: Vec<ManuscriptBlock>,
    pub(crate) global_equalities: Vec<Equality>,
    pub(crate) macros: BTreeMap<SymbolName, MacroDefinition>,
}

fn definitions_only(
    r: Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>,
) -> Option<Result<(SymbolName, Span, ExplicitDefinition), InconsistentSymbolUse>> {
    match r {
        // An origin specification is either a reference or a
        // definition, depending on how it is used.  But we will cope
        // with origin definitions when processing the blocks (as
        // opposed to the blocks' contents).
        Ok((
            _,
            _,
            SymbolUse::Definition(ExplicitDefinition::Origin(_, _)) | SymbolUse::Reference(_),
        )) => None,
        Ok((name, span, SymbolUse::Definition(def))) => Some(Ok((name, span, def))),
        Err(e) => Some(Err(e)),
    }
}

fn offset_to_block_id<T>((offset, item): (usize, T)) -> (BlockIdentifier, T) {
    (BlockIdentifier::from(offset), item)
}

impl SourceFile {
    fn symbol_uses(
        &self,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + use<'_>
    {
        let uses_in_instructions = self
            .blocks
            .iter()
            .enumerate()
            .map(offset_to_block_id)
            .flat_map(move |(block_id, block)| block.symbol_uses(block_id));
        let uses_in_global_assignments = self
            .global_equalities
            .iter()
            .flat_map(|eq| eq.symbol_uses());
        uses_in_instructions.chain(uses_in_global_assignments)
    }

    pub(crate) fn build_local_symbol_tables(
        &mut self,
    ) -> Result<(), OneOrMore<SymbolTableBuildFailure>> {
        let mut errors = Vec::default();
        for (block_identifier, block) in self.blocks.iter_mut().enumerate().map(offset_to_block_id)
        {
            if let Err(e) = block.build_local_symbol_tables(block_identifier) {
                errors.extend(e.into_iter());
            }
        }
        match OneOrMore::try_from_vec(errors) {
            Err(_) => Ok(()), // error vector is empty
            Ok(errors) => Err(errors),
        }
    }

    pub(crate) fn global_symbol_references(
        &self,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolContext), InconsistentSymbolUse>> + '_
    {
        fn accept_references_only(
            r: Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>,
        ) -> Option<Result<(SymbolName, Span, SymbolContext), InconsistentSymbolUse>> {
            match r {
                Ok((name, span, sym_use)) => match sym_use {
                    SymbolUse::Reference(context) => Some(Ok((name, span, context))),
                    // An origin specification is either a reference or a definition, depending on how it is used.
                    SymbolUse::Definition(ExplicitDefinition::Origin(
                        ref origin @ Origin::Symbolic(span, ref name),
                        block_id,
                    )) => Some(Ok((
                        name.clone(),
                        span,
                        SymbolContext::origin(block_id, origin.clone()),
                    ))),
                    SymbolUse::Definition(_) => None,
                },
                Err(e) => Some(Err(e)),
            }
        }
        self.symbol_uses().filter_map(accept_references_only)
    }

    pub(crate) fn global_symbol_definitions(
        &self,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, ExplicitDefinition), InconsistentSymbolUse>> + '_
    {
        self.symbol_uses().filter_map(definitions_only)
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
    fn symbol_uses(
        &self,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        [Ok((
            self.name.clone(),
            self.span,
            SymbolUse::Definition(
                // TODO: the expression.clone() on the next line is expensive.
                ExplicitDefinition::Equality(self.value.clone()),
            ),
        ))]
        .into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptLine {
    Meta(ManuscriptMetaCommand),
    Macro(MacroInvocation),
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
    pub(crate) body: Vec<MacroBodyLine>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MacroBodyLine {
    Expansion(MacroInvocation),
    Instruction(TaggedProgramInstruction),
    Equality(Equality),
}

impl MacroDefinition {
    pub(super) fn substitute_macro_parameters(
        &self,
        bindings: &MacroParameterBindings,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> InstructionSequence {
        let mut local_symbols = ExplicitSymbolTable::default();
        let mut instructions: Vec<TaggedProgramInstruction> = Vec::with_capacity(self.body.len());
        for body_line in self.body.iter() {
            match body_line {
                MacroBodyLine::Expansion(_macro_invocation) => {
                    unimplemented!("recursive macros are not yet supported")
                }
                MacroBodyLine::Instruction(tagged_program_instruction) => {
                    if let Some(tagged_program_instruction) = tagged_program_instruction
                        .substitute_macro_parameters(
                            bindings,
                            OnUnboundMacroParameter::ElideReference,
                            macros,
                        )
                    {
                        instructions.push(tagged_program_instruction);
                    } else {
                        // The instruction referred to an unbound
                        // macro parameter, and therefore the
                        // instruction is omitted.
                        //
                        // This is required by the text of the first
                        // paragraph of section 6-4 "MACRO
                        // INSTRUCTIONS" of the TX-2 User's Handbook.
                        // Also item (4) in section 6-4.6 ("The
                        // Defining Subprogram").
                    }
                }
                // Equalities and tags which occur inside the body of
                // a macro are not visible outside it.
                MacroBodyLine::Equality(Equality {
                    span: _,
                    name,
                    value,
                }) => {
                    let value: EqualityValue = value.substitute_macro_parameters(bindings, macros);
                    if let Err(e) =
                        local_symbols.define(name.clone(), ExplicitDefinition::Equality(value))
                    {
                        // We do not expect this to fail because only
                        // tag definitions can be invalid, equalities
                        // cannot (as long as the right-hand-side can
                        // be parsed, which has already happened).
                        panic!("unexpected failure when defining equality for {name} inside a macro body: {e}");
                    }
                }
            }
        }
        InstructionSequence {
            // build_local_symbol_tables extracts tags and propagates
            // them into the local symbol table, so this is not the
            // final version of the local symbol table.
            local_symbols: Some(local_symbols),
            instructions,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum MacroParameterValue {
    Value(Script, ArithmeticExpression),
    // TODO: bindings representing sequences of instructions (see for
    // example the SQ/NSQ example in the Users Handbook).
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct MacroParameterBindings {
    // TODO: all bindings should have a span, even if the parameter is
    // unset (in which case the span should correspond to the location
    // where the parameter would have been supplied.
    inner: BTreeMap<SymbolName, (Span, Option<MacroParameterValue>)>,
}

impl MacroParameterBindings {
    pub(super) fn insert(
        &mut self,
        name: SymbolName,
        span: Span,
        value: Option<MacroParameterValue>,
    ) {
        self.inner.insert(name, (span, value));
    }

    pub(super) fn get(&self, name: &SymbolName) -> Option<&(Span, Option<MacroParameterValue>)> {
        self.inner.get(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MacroInvocation {
    pub(crate) macro_def: MacroDefinition,
    pub(crate) param_values: MacroParameterBindings,
}

impl MacroInvocation {
    pub(super) fn substitute_macro_parameters(
        &self,
        macros: &BTreeMap<SymbolName, MacroDefinition>,
    ) -> InstructionSequence {
        self.macro_def
            .substitute_macro_parameters(&self.param_values, macros)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ManuscriptBlock {
    pub(crate) origin: Option<Origin>,
    // Macro invocations generate an InstructionSequence::Scoped(),
    // and since a single block may contain more than one macro
    // invocation, a block must comprise a sequence of
    // InstructionSequence instances.
    pub(crate) sequences: Vec<InstructionSequence>,
}

impl ManuscriptBlock {
    fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> {
        let mut result: Vec<Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> =
            Vec::new();
        if let Some(origin) = self.origin.as_ref() {
            result.extend(origin.symbol_uses(block_id));
        }
        result.extend(
            self.sequences
                .iter()
                .flat_map(|seq| seq.symbol_uses(block_id)),
        );
        result.into_iter()
    }

    fn build_local_symbol_tables(
        &mut self,
        block_identifier: BlockIdentifier,
    ) -> Result<(), OneOrMore<SymbolTableBuildFailure>> {
        let mut errors: Vec<SymbolTableBuildFailure> = Vec::new();
        for seq in self.sequences.iter_mut() {
            if let Some(local_symbols) = seq.local_symbols.as_mut() {
                match build_local_symbol_table(block_identifier, seq.instructions.iter()) {
                    Ok(more_symbols) => match local_symbols.merge(more_symbols) {
                        Ok(()) => (),
                        Err(e) => {
                            errors.extend(e.into_iter().map(SymbolTableBuildFailure::BadDefinition))
                        }
                    },
                    Err(e) => {
                        errors.extend(e.into_iter());
                    }
                }
            }
        }
        match OneOrMore::try_from_vec(errors) {
            Ok(errors) => Err(errors),
            Err(_) => Ok(()),
        }
    }

    pub(crate) fn instruction_count(&self) -> Unsigned18Bit {
        self.sequences
            .iter()
            .map(|seq| seq.emitted_word_count())
            .sum()
    }

    pub(crate) fn origin_span(&self) -> Span {
        if let Some(origin) = self.origin.as_ref() {
            origin.span()
        } else {
            if let Some(s) = self.sequences.first() {
                if let Some(first) = s.first() {
                    return first.span();
                }
            }
            Span::from(0..0)
        }
    }

    pub(super) fn push_unscoped_instruction(&mut self, inst: TaggedProgramInstruction) {
        if let Some(InstructionSequence {
            local_symbols: None,
            instructions,
        }) = self.sequences.last_mut()
        {
            instructions.push(inst);
        } else {
            self.sequences.push(InstructionSequence {
                local_symbols: None,
                instructions: vec![inst],
            });
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
    pub(crate) equalities: Vec<Equality>,
    pub(crate) entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn new(
        blocks: BTreeMap<BlockIdentifier, LocatedBlock>,
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
            .map(|block| block.following_addr())
            .max()
            .unwrap_or_else(Origin::default_address)
    }

    pub(crate) fn entry_point(&self) -> Option<Address> {
        self.entry_point
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LocatedBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) location: Address,
    pub(crate) sequences: Vec<InstructionSequence>,
}

impl LocatedBlock {
    pub(crate) fn emitted_word_count(&self) -> Unsigned18Bit {
        self.sequences
            .iter()
            .map(|seq| seq.emitted_word_count())
            .sum()
    }

    pub(crate) fn following_addr(&self) -> Address {
        self.location.index_by(self.emitted_word_count())
    }
}
