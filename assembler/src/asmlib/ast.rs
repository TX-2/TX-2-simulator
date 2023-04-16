///! Abstract syntax representation.   It's mostly not actually a tree.
use std::fmt::{self, Display, Formatter, Octal, Write};

use base::charset::{subscript_char, superscript_char};
use base::prelude::*;

use crate::ek;
use crate::state::NumeralMode;

/// Eventually we will support symbolic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LiteralValue {
    elevation: Elevation,
    value: Unsigned36Bit,
}

impl LiteralValue {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value << self.elevation.shift()
    }
}

impl From<(Elevation, Unsigned36Bit)> for LiteralValue {
    fn from((elevation, value): (Elevation, Unsigned36Bit)) -> LiteralValue {
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
fn format_elevated_chars(f: &mut Formatter<'_>, elevation: &Elevation, s: &str) -> fmt::Result {
    match elevation {
        Elevation::Normal => {
            f.write_str(s)?;
        }
        Elevation::Superscript => {
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
        Elevation::Subscript => {
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

/// Eventually we will support symbolic expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Expression {
    Literal(LiteralValue),
}

impl Expression {
    fn value(&self) -> Unsigned36Bit {
        match self {
            Expression::Literal(literal) => literal.value(),
        }
    }
}

impl From<LiteralValue> for Expression {
    fn from(literal: LiteralValue) -> Expression {
        Expression::Literal(literal)
    }
}

impl From<(Elevation, Unsigned36Bit)> for Expression {
    fn from((e, v): (Elevation, Unsigned36Bit)) -> Expression {
        Expression::from(LiteralValue::from((e, v)))
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Literal(value) => value.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Elevation {
    Superscript, // e.g. config values
    Normal,      // e.g. the address part of an instruction
    Subscript,   // e.g. the index bits
}

impl Elevation {
    fn shift(&self) -> u32 {
        match self {
            Elevation::Superscript => 30, // This is a config value.
            Elevation::Subscript => 18,   // This is an index value
            Elevation::Normal => 0,       // e.g. an address value
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InstructionFragment {
    pub(crate) value: Expression,
}

impl InstructionFragment {
    pub(crate) fn value(&self) -> Unsigned36Bit {
        self.value.value()
    }
}

impl From<(Elevation, Unsigned36Bit)> for InstructionFragment {
    fn from((e, v): (Elevation, Unsigned36Bit)) -> InstructionFragment {
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

#[derive(Debug, Clone, Eq, PartialOrd, Ord)]
pub(crate) struct SymbolName {
    pub(crate) canonical: String,
    // pub(crate) as_used: String,
}

impl std::fmt::Display for SymbolName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.canonical.fmt(f)
    }
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &SymbolName) -> bool {
        self.canonical.eq(&other.canonical)
    }
}

impl<'a, 'b> SymbolName {
    // Symexes "TYPE A" and "TYPEA" are equivalent.
    fn canonical(span: &ek::LocatedSpan<'a, 'b>) -> String {
        (*span.fragment())
            .chars()
            .filter(|ch: &char| -> bool { *ch != ' ' })
            .collect()
    }
}

impl<'a, 'b> From<&ek::LocatedSpan<'a, 'b>> for SymbolName {
    fn from(location: &ek::LocatedSpan<'a, 'b>) -> SymbolName {
        SymbolName {
            canonical: SymbolName::canonical(location),
            //as_used: location.fragment().to_string(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct Origin(pub Address);

impl From<Origin> for Address {
    fn from(orig: Origin) -> Address {
        orig.0
    }
}

impl From<Origin> for Unsigned18Bit {
    fn from(orig: Origin) -> Unsigned18Bit {
        Unsigned18Bit::from(Address::from(orig))
    }
}

impl Default for Origin {
    fn default() -> Origin {
        // Section 6-2.5 of the User Manual states that if the
        // manuscript contains no origin specification (no vertical
        // bar) the whole program is located (correctly) at 200_000
        // octal.
        Origin(Address::new(u18!(0o200_000)))
    }
}

impl Display for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(&self.0, f)
    }
}

impl Octal for Origin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:o}", self.0)
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
    pub(crate) fn value(&self) -> Unsigned36Bit {
        let word = self
            .parts
            .iter()
            .fold(Unsigned36Bit::ZERO, |acc, frag| acc | frag.value());
        match self.holdbit {
            HoldBit::Hold => word | HELD_MASK,
            HoldBit::NotHold => word & !HELD_MASK,
            HoldBit::Unspecified => word,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourceFile {
    pub(crate) punch: Option<PunchCommand>,
    pub(crate) blocks: Vec<ManuscriptBlock>,
}

impl SourceFile {
    pub(crate) fn empty() -> SourceFile {
        SourceFile {
            blocks: Vec::new(),
            punch: None,
        }
    }

    pub(crate) fn global_symbol_definitions(
        &self,
    ) -> impl Iterator<Item = (&SymbolName, &Expression)> {
        self.blocks
            .iter()
            .flat_map(|block| block.global_symbol_definitions())
    }
}

/// Represents the ☛☛PUNCH metacommand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PunchCommand(pub(crate) Option<Address>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ManuscriptMetaCommand {
    Invalid, // e.g."☛☛BOGUS"
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
    Assignment(SymbolName, Expression), // User Guide calles these "equalities".
    Instruction(ProgramInstruction),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ManuscriptBlock {
    pub(crate) origin: Option<Origin>,
    pub(crate) statements: Vec<Statement>,
}

impl ManuscriptBlock {
    pub(crate) fn global_symbol_definitions(
        &self,
    ) -> impl Iterator<Item = (&SymbolName, &Expression)> {
        self.statements
            .iter()
            .filter_map(|statement: &Statement| match statement {
                Statement::Assignment(symbol_name, expression) => Some((symbol_name, expression)),
                _ => None,
            })
    }
}

#[derive(Debug)]
pub(crate) struct Directive {
    // items must be in manuscript order, because RC block addresses
    // are assigned in the order they appear in the code, and
    // similarly for undefined origins (e.g. "FOO| JMP ..." where FOO
    // has no definition).
    pub(crate) blocks: Vec<Block>,
    entry_point: Option<Address>,
}

impl Directive {
    pub(crate) fn new() -> Directive {
        Directive {
            blocks: Vec::new(),
            entry_point: None,
        }
    }

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

#[derive(Debug, Default, Clone, PartialEq, Eq)]
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
