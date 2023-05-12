///! Abstract syntax representation.   It's mostly not actually a tree.
use std::borrow::Cow;
use std::fmt::{self, Display, Formatter, Octal, Write};
use std::hash::Hash;
use std::ops::Shl;

use base::charset::{subscript_char, superscript_char, Script};
use base::prelude::*;

use super::state::NumeralMode;
use super::symbol::SymbolName;
use super::symtab::{Evaluate, SymbolContext, SymbolDefinition, SymbolLookup, SymbolUse};

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
    elevation: Script,
    value: Unsigned36Bit,
}

impl LiteralValue {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value << self.elevation.shift()
    }
}

impl Evaluate for LiteralValue {
    fn evaluate<S: SymbolLookup>(&self, _: &mut S) -> Result<Unsigned36Bit, S::Error> {
        Ok(self.value())
    }
}

impl From<(Script, Unsigned36Bit)> for LiteralValue {
    fn from((elevation, value): (Script, Unsigned36Bit)) -> LiteralValue {
        LiteralValue { elevation, value }
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

/// Eventually we will support real expressions, but for now we only
/// suport literals and references to symbols ("equalities" in the
/// User Handbook).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expression {
    Literal(LiteralValue),
    Symbol(Script, SymbolName),
}

impl Expression {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Expression::Literal(_value) => (),
            Expression::Symbol(script, symbol_name) => {
                result.push((
                    symbol_name.clone(),
                    SymbolUse::Reference(SymbolContext::from(script)),
                ));
            }
        }
        result.into_iter()
    }
}

impl Evaluate for Expression {
    fn evaluate<S: SymbolLookup>(&self, symtab: &mut S) -> Result<Unsigned36Bit, S::Error> {
        match self {
            Expression::Literal(literal) => Ok(literal.value()),
            Expression::Symbol(elevation, name) => {
                let context = SymbolContext::from(elevation);
                symtab
                    .lookup(name, &context)
                    .map(|value| value.shl(elevation.shift()))
            }
        }
    }
}

impl From<LiteralValue> for Expression {
    fn from(literal: LiteralValue) -> Expression {
        Expression::Literal(literal)
    }
}

impl From<(Script, Unsigned36Bit)> for Expression {
    fn from((e, v): (Script, Unsigned36Bit)) -> Expression {
        Expression::from(LiteralValue::from((e, v)))
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

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Literal(value) => value.fmt(f),
            Expression::Symbol(elevation, name) => {
                elevated_string(&name.to_string(), elevation).fmt(f)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstructionFragment {
    pub(crate) value: Expression,
}

impl InstructionFragment {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        self.value.symbol_uses()
    }
}

impl Evaluate for InstructionFragment {
    fn evaluate<S: SymbolLookup>(&self, symtab: &mut S) -> Result<Unsigned36Bit, S::Error> {
        self.value.evaluate(symtab)
    }
}

impl From<(Script, Unsigned36Bit)> for InstructionFragment {
    fn from((e, v): (Script, Unsigned36Bit)) -> InstructionFragment {
        InstructionFragment {
            value: Expression::from((e, v)),
        }
    }
}

impl From<Expression> for InstructionFragment {
    fn from(e: Expression) -> Self {
        Self { value: e }
    }
}

// Once we support symbolic origins we should update
// ManuscriptBlock::global_symbol_definitions() to expose them.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub(crate) enum Origin {
    Literal(Address),
    Symbolic(SymbolName),
}

impl Default for Origin {
    fn default() -> Origin {
        Origin::Literal(Origin::default_address())
    }
}

impl Display for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Origin::Literal(addr) => fmt::Display::fmt(&addr, f),
            Origin::Symbolic(sym) => fmt::Display::fmt(&sym, f),
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

impl Octal for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Origin::Literal(address) => fmt::Octal::fmt(&address, f),
            Origin::Symbolic(name) => fmt::Display::fmt(&name, f),
        }
    }
}

impl Origin {
    pub(crate) fn symbol_uses(
        &self,
        block: usize,
    ) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        let mut result = Vec::with_capacity(1);
        match self {
            Origin::Literal(_) => (),
            Origin::Symbolic(name) => {
                result.push((name.clone(), SymbolUse::Origin(name.clone(), block)))
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
pub(crate) struct ProgramInstruction {
    pub(crate) tag: Option<SymbolName>,
    pub(crate) holdbit: HoldBit,
    pub(crate) parts: Vec<InstructionFragment>,
}

const HELD_MASK: Unsigned36Bit = u36!(1 << 35);

impl ProgramInstruction {
    pub(crate) fn value<S: SymbolLookup>(&self, symtab: &mut S) -> Result<Unsigned36Bit, S::Error> {
        fn or_looked_up_value<S: SymbolLookup>(
            accumulator: Result<Unsigned36Bit, S::Error>,
            frag: &InstructionFragment,
            symtab: &mut S,
        ) -> Result<Unsigned36Bit, S::Error> {
            accumulator.and_then(|acc| Ok(acc | frag.value.evaluate(symtab)?))
        }

        self.parts
            .iter()
            .fold(Ok(Unsigned36Bit::ZERO), |acc, curr| {
                or_looked_up_value(acc, curr, symtab)
            })
            .map(|word| match self.holdbit {
                HoldBit::Hold => word | HELD_MASK,
                HoldBit::NotHold => word & !HELD_MASK,
                HoldBit::Unspecified => word,
            })
    }

    pub(crate) fn symbol_uses(
        &self,
        block: usize,
        offset: usize,
    ) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        let mut result = Vec::with_capacity(self.parts.len() + 1);
        if let Some(name) = self.tag.as_ref() {
            let tagdef = SymbolDefinition::Tag { block, offset };
            result.push((name.clone(), SymbolUse::Definition(tagdef)));
        }
        result.extend(self.parts.iter().flat_map(|frag| frag.symbol_uses()));
        result.into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    pub(crate) blocks: Vec<ManuscriptBlock>,
}

impl SourceFile {
    pub(crate) fn symbol_uses(&self) -> impl Iterator<Item = (SymbolName, SymbolUse)> + '_ {
        self.blocks
            .iter()
            .enumerate()
            .flat_map(|(block_number, block)| block.symbol_uses(block_number))
    }

    pub(crate) fn global_symbol_references(
        &self,
    ) -> impl Iterator<Item = (SymbolName, SymbolContext)> + '_ {
        self.symbol_uses()
            .filter_map(|(name, sym_use)| match sym_use {
                SymbolUse::Reference(context) => Some((name, context)),
                SymbolUse::Definition(_) => None,
                // An origin specification is either a reference or a definition, depending on how it is used.
                SymbolUse::Origin(name, block) => Some((name, SymbolContext::origin(block))),
            })
    }

    pub(crate) fn global_symbol_definitions(
        &self,
    ) -> impl Iterator<Item = (SymbolName, SymbolDefinition)> + '_ {
        self.symbol_uses()
            .filter_map(|(name, sym_use)| match sym_use {
                SymbolUse::Reference(_context) => None,
                SymbolUse::Definition(def) => Some((name, def)),
                // An origin specification is either a reference or a definition, depending on how it is used.
                SymbolUse::Origin(name, block) => Some((
                    name,
                    SymbolDefinition::Undefined(SymbolContext::origin(block)),
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
    Assignment(SymbolName, Expression), // User Guide calls these "equalities".
    Instruction(ProgramInstruction),
}

impl Statement {
    fn memory_size(&self) -> usize {
        match self {
            Statement::Assignment(_, _) => 0,
            Statement::Instruction(_) => 1,
        }
    }

    pub(crate) fn symbol_uses(
        &self,
        block: usize,
        offset: usize,
    ) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        match self {
            Statement::Assignment(symbol, expression) => {
                vec![(
                    symbol.clone(),
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
    ) -> impl Iterator<Item = (SymbolName, SymbolUse)> {
        let mut result: Vec<(SymbolName, SymbolUse)> = Vec::new();
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) origin: Origin,
    pub(crate) items: Vec<ProgramInstruction>,
}

impl Block {
    pub(crate) fn push(&mut self, inst: ProgramInstruction) {
        self.items.push(inst);
    }

    pub(crate) fn instruction_count(&self) -> usize {
        self.items.len()
    }
}
