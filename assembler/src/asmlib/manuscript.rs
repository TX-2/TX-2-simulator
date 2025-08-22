use std::collections::BTreeMap;

use tracing::{Level, event};

use base::Unsigned18Bit;
#[cfg(test)]
use base::Unsigned36Bit;
use base::charset::Script;
use base::prelude::Address;
#[cfg(test)]
use base::u18;

use super::ast::ArithmeticExpression;
use super::ast::Equality;
use super::ast::EqualityValue;
#[cfg(test)]
use super::ast::HoldBit;
#[cfg(test)]
use super::ast::InstructionFragment;
use super::ast::InstructionSequence;
use super::ast::OnUnboundMacroParameter;
use super::ast::Origin;
use super::ast::SymbolTableBuildFailure;
use super::ast::SymbolUse;
use super::ast::Tag;
use super::ast::TaggedProgramInstruction;
use super::ast::block_items_with_offset;
use super::collections::OneOrMore;
use super::directive::Directive;
use super::lexer::Token;
use super::memorymap::LocatedBlock;
use super::memorymap::MemoryMap;
use super::span::Span;
use super::span::Spanned;
#[cfg(test)]
use super::span::span;
use super::state::NumeralMode;
use super::symbol::InconsistentSymbolUse;
use super::symbol::SymbolContext;
use super::symbol::SymbolName;
#[cfg(test)]
use super::symtab::BadSymbolDefinition;
use super::symtab::ExplicitDefinition;
use super::symtab::ExplicitSymbolTable;
#[cfg(test)]
use super::symtab::TagDefinition;
use super::types::AssemblerFailure;
use super::types::BlockIdentifier;

fn offset_to_block_id<T>((offset, item): (usize, T)) -> (BlockIdentifier, T) {
    (BlockIdentifier::from(offset), item)
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

    pub(crate) fn into_directive(self, mem_map: &MemoryMap) -> Result<Directive, AssemblerFailure> {
        let SourceFile {
            punch,
            blocks: input_blocks,
            global_equalities: equalities,
            macros: _,
        } = self;
        let output_blocks: BTreeMap<BlockIdentifier, LocatedBlock> = input_blocks
            .into_iter()
            .enumerate()
            .map(|(id, mblock)| (BlockIdentifier::from(id), mblock))
            .map(|(block_id, mblock)| {
                let location: Address = match mem_map.get(&block_id).map(|pos| pos.block_address) {
                    Some(Some(addr)) => addr,
                    None => unreachable!("unknown block {block_id} in input_blocks"),
                    Some(None) => unreachable!(
                        "block location for {block_id} should already have been determined"
                    ),
                };
                (
                    block_id,
                    LocatedBlock {
                        origin: mblock.origin,
                        location,
                        sequences: mblock.sequences,
                    },
                )
            })
            .collect();

        let entry_point: Option<Address> = match punch {
            Some(PunchCommand(Some(address))) => {
                event!(
                    Level::INFO,
                    "program entry point was specified as {address:o}"
                );
                Some(address)
            }
            Some(PunchCommand(None)) => {
                event!(Level::INFO, "program entry point was not specified");
                None
            }
            None => {
                event!(
                    Level::WARN,
                    "No PUNCH directive was given, program has no start address"
                );
                None
            }
        };

        // Because the PUNCH instruction causes the assembler
        // output to be punched to tape, this effectively
        // marks the end of the input.  On the real M4
        // assembler it is likely possible for there to be
        // more manuscript after the PUNCH metacommand, and
        // for this to generate a fresh reader leader and so
        // on.  But this is not supported here.  The reason we
        // don't support it is that we'd need to know the
        // answers to a lot of questions we don't have
        // answers for right now.  For example, should the
        // existing program be cleared?  Should the symbol
        // table be cleared?
        Ok(Directive::new(output_blocks, equalities, entry_point))
    }
}

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
    pub(super) fn symbol_uses(
        &self,
        block_id: BlockIdentifier,
    ) -> impl Iterator<Item = Result<(SymbolName, Span, SymbolUse), InconsistentSymbolUse>> + use<>
    {
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
            if let Some(s) = self.sequences.first()
                && let Some(first) = s.first()
            {
                return first.span();
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
    // TODO: we should probably not be depending here on an
    // implementation artifact of the lexer (i.e. Token).
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
    fn substitute_macro_parameters(
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
                        panic!(
                            "unexpected failure when defining equality for {name} inside a macro body: {e}"
                        );
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
    pub(crate) fn insert(
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

fn expand_macro(
    invocation: &MacroInvocation,
    macros: &BTreeMap<SymbolName, MacroDefinition>,
) -> InstructionSequence {
    invocation.substitute_macro_parameters(macros)
}

pub(crate) fn manuscript_lines_to_source_file<'a>(
    lines: Vec<(Span, ManuscriptLine)>,
) -> Result<SourceFile, chumsky::error::Rich<'a, super::lexer::Token>> {
    let mut blocks: Vec<ManuscriptBlock> = Vec::new();
    let mut equalities: Vec<Equality> = Vec::new();
    let mut macros: BTreeMap<SymbolName, MacroDefinition> = Default::default();
    let mut maybe_punch: Option<PunchCommand> = None;

    fn get_or_create_output_block(result: &mut Vec<ManuscriptBlock>) -> &mut ManuscriptBlock {
        if result.is_empty() {
            result.push(ManuscriptBlock {
                origin: None,
                sequences: Vec::new(),
            });
        }
        result
            .last_mut()
            .expect("result cannot be empty because we just pushed an item onto it")
    }

    fn begin_new_block(origin: Origin, result: &mut Vec<ManuscriptBlock>) -> &mut ManuscriptBlock {
        result.push(ManuscriptBlock {
            origin: Some(origin),
            sequences: Vec::new(),
        });
        result
            .last_mut()
            .expect("result cannot be empty because we just pushed an item onto it")
    }

    fn prepend_tags(v: &mut Vec<Tag>, initial: &mut Vec<Tag>) {
        let alltags: Vec<Tag> = initial.drain(0..).chain(v.drain(0..)).collect();
        v.extend(alltags);
    }

    let mut pending_tags: Vec<Tag> = Vec::new();

    let bad_tag_pos = |tag: Tag| {
        let tag_name = &tag.name;
        chumsky::error::Rich::custom(
            tag.span,
            format!("tag {tag_name} must be followed by an instruction"),
        )
    };

    for (_span, line) in lines {
        match line {
            ManuscriptLine::Macro(invocation) => {
                get_or_create_output_block(&mut blocks)
                    .sequences
                    .push(expand_macro(&invocation, &macros));
            }
            ManuscriptLine::TagsOnly(tags) => {
                pending_tags.extend(tags);
            }

            ManuscriptLine::Meta(_)
            | ManuscriptLine::OriginOnly(_)
            | ManuscriptLine::OriginAndStatement(_, _)
            | ManuscriptLine::Eq(_)
                if !pending_tags.is_empty() =>
            {
                return Err(bad_tag_pos(
                    pending_tags
                        .pop()
                        .expect("we know pending_tags is non-empty"),
                ));
            }

            ManuscriptLine::Meta(ManuscriptMetaCommand::Punch(punch)) => {
                maybe_punch = Some(punch);
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::BaseChange(_)) => {
                // These already took effect on the statements which
                // were parsed following them, so no need to keep them
                // now.
            }
            ManuscriptLine::Meta(ManuscriptMetaCommand::Macro(macro_def)) => {
                if let Some(previous) = macros.insert(macro_def.name.clone(), macro_def) {
                    event!(Level::INFO, "Redefinition of macro {}", &previous.name);
                }
            }

            ManuscriptLine::OriginOnly(origin) => {
                begin_new_block(origin, &mut blocks);
            }
            ManuscriptLine::StatementOnly(mut tagged_program_instruction) => {
                prepend_tags(&mut tagged_program_instruction.tags, &mut pending_tags);
                get_or_create_output_block(&mut blocks)
                    .push_unscoped_instruction(tagged_program_instruction);
            }
            ManuscriptLine::OriginAndStatement(origin, statement) => {
                begin_new_block(origin, &mut blocks).push_unscoped_instruction(statement);
            }
            ManuscriptLine::Eq(equality) => {
                equalities.push(equality);
            }
        }
    }
    if let Some(t) = pending_tags.pop() {
        return Err(bad_tag_pos(t));
    }

    Ok(SourceFile {
        punch: maybe_punch,
        blocks,
        global_equalities: equalities,
        macros,
    })
}
