use std::collections::HashMap;

use chumsky::{
    DefaultExpected,
    error::LabelError,
    extension::v1::{Ext, ExtParser},
    extra::{Full, ParserExtra},
    input::{Cursor, InputRef, Stream, ValueInput},
    prelude::*,
};

use base::charset::Script;

use super::{
    super::{
        ast::ArithmeticExpression,
        manuscript::{
            MacroBodyLine, MacroDefinition, MacroDummyParameters, MacroInvocation, MacroParameter,
            MacroParameterBindings, MacroParameterValue,
        },
        state::State,
        symbol::SymbolName,
    },
    ExtraWithoutContext, Grammar, MacroBody, Metacommand, Mi, MyError, MyErrorVec, Span,
    arithmetic_expression_in_any_script_allowing_spaces, end_of_line, grammar, lexer,
    named_metacommand, named_symbol,
    symex::{self, SymexSyllableRule},
    tokenize, tokenize_and_parse_with,
};

pub(crate) struct UnparsedMacroDefinitionsParser_;

use lexer::Token as Tok;

fn discard_to_eol<'src, 'p, I, E>(inp: &mut InputRef<'src, 'p, I, E>)
where
    I: Input<'src, Token = Tok, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    while let Some(t) = inp.next_maybe().as_deref() {
        if t == &Tok::Newline {
            return;
        }
    }
}

// Read and discard tokens until we find ☛☛ at the start of a line or
// at the start of input.  Return the position of the first ☛.
fn advance_to_double_hand<'src, 'p, I, E>(
    inp: &mut InputRef<'src, 'p, I, E>,
) -> Option<Cursor<'src, 'p, I>>
where
    I: Input<'src, Token = Tok, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    use super::Script::Normal;

    loop {
        let before = inp.cursor();
        match inp.next_maybe().as_deref() {
            None => {
                return None;
            }
            Some(first_tok) => {
                match first_tok {
                    Tok::Newline => {
                        // Since we found a newline, we don't want to
                        // call discard_to_eol.
                    }
                    Tok::Hand(Normal) => {
                        match inp.next_maybe().as_deref() {
                            None => {
                                return None;
                            }
                            Some(second_tok) => {
                                match second_tok {
                                    Tok::Newline => {
                                        // Since we found a newline, we don't
                                        // want to call discard_to_eol.
                                    }
                                    Tok::Hand(Normal) => {
                                        return Some(before);
                                    }
                                    _other => {
                                        discard_to_eol(inp);
                                    }
                                }
                            }
                        }
                    }
                    _other => {
                        discard_to_eol(inp);
                    }
                }
            }
        }
    }
}

// Read and discard tokens until we find ☛☛<expected_cmd> at the start
// of a line or at the start of input. The expected_cmd argument is
// the literal command name we expect to find.
fn advance_to_meta<'src, 'p, I, E>(
    expected_cmd: &str,
    inp: &mut InputRef<'src, 'p, I, E>,
) -> Result<Option<Cursor<'src, 'p, I>>, E::Error>
where
    I: Input<'src, Token = Tok, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    use super::Script::Normal;
    loop {
        let Some(before) = advance_to_double_hand(inp) else {
            // There are no more ☛☛
            return Ok(None);
        };
        match inp.next_maybe().as_deref() {
            found @ Some(Tok::SymexSyllable(Normal, actual_cmd)) => {
                if actual_cmd == expected_cmd {
                    return Ok(Some(before));
                } else if actual_cmd == "EMD" {
                    // We know we were not looking for EMD.  Hence
                    // we have seen ☛☛EMD before ☛☛DEF.  This is
                    // an error.
                    return Err(LabelError::<I, _>::expected_found(
                        [DefaultExpected::SomethingElse],
                        found.cloned().map(Into::into),
                        inp.span_since(&before),
                    ));
                }
                // Otherwise some other metacommand
                // (e.g. ☛☛DECIMAL).  Ignore.
            }
            None => {
                return if expected_cmd == "EMD" {
                    // EOF inside a macro body.  This is an error.
                    Err(LabelError::<I, _>::expected_found(
                        [DefaultExpected::SomethingElse],
                        None,
                        inp.span_since(&before),
                    ))
                } else {
                    // EOF while looking for ☛☛DEF.
                    Ok(None)
                };
            }
            Some(_other_tok) => {
                discard_to_eol(inp);
            }
        }
    }
}

impl<'src, I, E> ExtParser<'src, I, Vec<SimpleSpan>, E> for UnparsedMacroDefinitionsParser_
where
    I: Input<'src, Token = Tok, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    fn parse(&self, inp: &mut InputRef<'src, '_, I, E>) -> Result<Vec<SimpleSpan>, E::Error> {
        let mut macros = Vec::new();
        loop {
            match advance_to_meta("DEF", inp)? {
                Some(before) => match advance_to_meta("EMD", inp)? {
                    Some(_) => {
                        macros.push(inp.span_since(&before));
                    }
                    None => {
                        break;
                    }
                },
                None => {
                    break;
                }
            }
        }
        Ok(macros)
    }
}

pub(crate) type UnparsedMacroDefinitionsParser = Ext<UnparsedMacroDefinitionsParser_>;

pub(crate) fn unparsed_macro_definitions_parser() -> UnparsedMacroDefinitionsParser {
    Ext(UnparsedMacroDefinitionsParser_)
}

fn parse_unparsed_macro_definitions<'src, 'state>(
    source_file_body: &'src str,
    mut macros: Vec<SimpleSpan>,
    state: &'state mut State<'src>,
) -> Result<MyErrorVec<'src>, MyErrorVec<'src>>
where
    'src: 'state,
{
    fn convert_errors<T>(input: HashMap<SimpleSpan, Vec<T>>) -> Vec<T> {
        let mut tmp: Vec<(SimpleSpan, Vec<T>)> = input.into_iter().collect();
        tmp.sort_by_key(|(span, _)| span.start);
        tmp.into_iter().flat_map(|(_span, errs)| errs).collect()
    }

    let macro_count: usize = macros.len();
    let full_definition_parser = macro_definition();
    let mut per_definition_errors: HashMap<SimpleSpan, MyErrorVec<'src>> = HashMap::new();

    // `macros` contains the spans of all the macro definitions in the
    // input.  Programs are not required to define a macro before
    // calling it, so we may not be able, yet, to parse the body of
    // the first macro definition.  Instead, we try to parse them one
    // by one, and when we find one that we can parse, we accept it.
    //
    // If we cannot parse a macro, we continue, trying to parse the
    // remaining macro definitions.  We loop until either all
    // definitions were parsed or we cannot parse any of the remaining
    // macro definitions.
    let mut iteration_number: usize = 0;
    while !macros.is_empty() {
        assert!(
            iteration_number < macro_count,
            "algorithm is not making progress; this is iteration {iteration_number} but there were only {macro_count} macros to parse"
        );
        iteration_number += 1;

        let mut still_todo: Vec<SimpleSpan> = Vec::with_capacity(macros.len());
        let mut any_success = false;
        // Try to parse each of the macro definitions we have not yet
        // been able to parse (or have not yet attempted to parse).
        for macro_def_span in macros.drain(0..) {
            let (maybe_parsed, errors): (Option<MacroDefinition>, MyErrorVec) =
                parse_single_macro_definition(
                    &full_definition_parser,
                    source_file_body,
                    macro_def_span,
                    state,
                );
            per_definition_errors.insert(macro_def_span, errors);
            if let Some(macro_def) = maybe_parsed {
                // We parsed this one; record the fact that we made
                // progress in this iteration and record the
                // definition itself.
                any_success = true;
                // We record the macro definition in `state` so that
                // later invocations of `full_definition_parser` can
                // use the known macro definitions in its attempt to
                // parse this macro definition.
                state.define_macro(macro_def);
            } else {
                // Not successful this time; try again in the next
                // iteration if there is one.
                still_todo.push(macro_def_span);
            }
        }
        if any_success {
            // We made progress, so there will be another iteration.
            macros.extend(still_todo);
        } else {
            // We can no longer make progress.  There are macro
            // definitions that we cannot parse.
            return Err(convert_errors(per_definition_errors));
        }
    }
    // We have parsed all the macro definitions.  But we may still
    // have diagnostics, so return those.
    Ok(convert_errors(per_definition_errors))
}

/// Extract macrs defined in `source_file_body` and record them in
/// `state`.  Return Ok if all macro definitions can be parsed, Err if
/// at least one cannot.  In both the success and failure case, return
/// any diagnostics the parsers produced.
pub(crate) fn parse_unparsed_macro_definitions_only<'src, 'state>(
    source_file_body: &'src str,
    state: &'state mut State<'src>,
) -> Result<MyErrorVec<'src>, MyErrorVec<'src>>
where
    'src: 'state,
{
    let span_extraction_parser = unparsed_macro_definitions_parser();
    match tokenize_and_parse_with(source_file_body, 0, state, span_extraction_parser) {
        (None, errors) => Err(errors),
        (Some(macros), mut errors) => {
            match parse_unparsed_macro_definitions(source_file_body, macros, state) {
                Ok(mut new_errors) => {
                    errors.extend(new_errors.drain(0..));
                    Ok(errors)
                }
                Err(mut new_errors) => {
                    errors.extend(new_errors.drain(0..));
                    Err(errors)
                }
            }
        }
    }
}

// Exposed for testing.
fn macro_definition_dummy_parameter<'a, I>()
-> impl Parser<'a, I, MacroParameter, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // The TX-2 Users Handbook section 6-4.4 ("DUMMY PARAMETERS")
    // doesn't disallow spaces in macro argument names.
    (macro_terminator().then(named_symbol(SymexSyllableRule::Multiple, Script::Normal))).map_with(
        |(terminator, symbol), extra| MacroParameter {
            name: symbol,
            span: extra.span(),
            preceding_terminator: terminator,
        },
    )
}

fn macro_definition_dummy_parameters<'a, I>()
-> impl Parser<'a, I, MacroDummyParameters, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        macro_definition_dummy_parameter()
            .repeated()
            .at_least(1)
            .collect::<Vec<_>>()
            .map(MacroDummyParameters::OneOrMore),
        macro_terminator().map(MacroDummyParameters::Zero),
    ))
}

/// Macros are described in section 6-4 of the TX-2 User Handbook.
pub(super) fn macro_definition<'src, I>()
-> impl Parser<'src, I, MacroDefinition, ExtraWithoutContext<'src>> + use<'src, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    let g = grammar();
    named_metacommand(Metacommand::DefineMacro)
        .ignore_then(
            named_symbol(SymexSyllableRule::Multiple, Script::Normal).labelled("macro name"), // the macro's name (# is not allowed)
        )
        .then(macro_definition_dummy_parameters())
        .then_ignore(end_of_line())
        .then(macro_body(&g))
        .then_ignore(named_metacommand(Metacommand::EndMacroDefinition))
        .try_map(|((name, params), body), span| {
            Ok(MacroDefinition {
                name,
                params,
                body,
                span,
            })
        })
    // We don't parse end-of-line here because all metacommands are supposed
    // to be followed by end-of-line.
}

fn parse_single_macro_definition<'source, 'state, P>(
    macro_definition_parser: &P,
    whole_source: &'source str,
    macro_definition_span: SimpleSpan,
    state: &'state mut State<'source>,
) -> (Option<MacroDefinition>, Vec<MyError<'source, Mi>>)
where
    P: Parser<'source, Mi, MacroDefinition, ExtraWithoutContext<'source>>,
{
    let macro_def_span_begin: usize = macro_definition_span.start;
    let macro_def_span_end: usize = macro_definition_span.end;
    let macro_definition_source_fragment = &whole_source[macro_def_span_begin..macro_def_span_end];

    let spanned_tokens = tokenize(
        macro_definition_source_fragment,
        macro_definition_span.start,
    );
    let end_span: SimpleSpan = spanned_tokens
        .iter()
        .map(|(_, span)| span.end)
        .max()
        .map_or_else(
            || SimpleSpan::new(macro_definition_span.end, macro_definition_span.end),
            |end| SimpleSpan::new(end, end),
        );
    let token_stream: Mi = Stream::from_iter(spanned_tokens).map(end_span, |unchanged| unchanged);
    macro_definition_parser
        .parse_with_state(token_stream, state)
        .into_output_errors()
}

/// Macro terminators are described in section 6-4.5 of the TX-2 User Handbook.
fn macro_terminator<'a, I>() -> impl Parser<'a, I, Tok, ExtraWithoutContext<'a>>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    // This list of 16 allowed terminators is exhaustive, see section
    // 6-4.5 of the TX-2 User Handbook.
    //
    // ☛ , = →  | ⊃ ≡ ~ < > ∩ ∪ / × ∨ ∧
    //
    // The second symbol, in my scanned copy of the Users Handbook
    // (page 6-31 of the Nov 1963 Users Handbook), looks like either a
    // comma or a dot/full-stop/period.  Since a dot is valid in a
    // symex name, and because the symbol seems to be taller than it
    // is wide, I'm going to assume it is a comma.
    //
    // They are actually hard to distinguish in the copy of the Users
    // Handbook I have.  But, looking at page 011 of Leonard
    // Kleinrock's listing for his network simulator, the `HP OS`
    // macro is definitely using as a separator a symbol that lives on
    // the line.  If you look a little further below on the same
    // page, the third instruction in the body of the `MV MX` macro
    // body contains both a dot and a comma.  The dot is definitely
    // above the line and looks rounder.  So I conclude that the
    // separator character is a comma.
    choice((
        just(Tok::Hand(Script::Normal)),
        just(Tok::Comma(Script::Normal)),
        just(Tok::Equals(Script::Normal)),
        just(Tok::Arrow(Script::Normal)),
        just(Tok::Pipe(Script::Normal)),
        just(Tok::ProperSuperset(Script::Normal)),
        just(Tok::IdenticalTo(Script::Normal)),
        just(Tok::Tilde(Script::Normal)),
        just(Tok::LessThan(Script::Normal)),
        just(Tok::GreaterThan(Script::Normal)),
        just(Tok::Intersection(Script::Normal)),
        just(Tok::Union(Script::Normal)),
        just(Tok::Solidus(Script::Normal)),
        just(Tok::Times(Script::Normal)),
        just(Tok::LogicalOr(Script::Normal)),
        just(Tok::LogicalAnd(Script::Normal)),
    ))
    .labelled("macro terminator")
}

fn macro_body<'a, 'b, I>(
    grammar: &Grammar<'a, 'b, I>,
) -> impl Parser<'a, I, MacroBody, ExtraWithoutContext<'a>> + use<'a, 'b, I>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    let parser = (macro_body_line(grammar).then_ignore(end_of_line()))
        .repeated()
        .collect::<Vec<MacroBodyLine>>()
        .map(MacroBody::from);
    parser.labelled("macro body")
}

fn macro_body_line<'a, 'b, I>(
    grammar: &Grammar<'a, 'b, I>,
) -> impl Parser<'a, I, MacroBodyLine, ExtraWithoutContext<'a>> + use<'a, 'b, I>
where
    I: Input<'a, Token = Tok, Span = Span> + ValueInput<'a>,
{
    choice((
        macro_invocation().map(MacroBodyLine::Expansion),
        grammar.assignment.clone().map(MacroBodyLine::Equality),
        grammar
            .tagged_program_instruction
            .clone()
            .map(MacroBodyLine::Instruction),
    ))
}

pub(super) fn macro_invocation<'src, I>()
-> impl Parser<'src, I, MacroInvocation, ExtraWithoutContext<'src>>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    Ext(MacroInvocationParser::default())
}

type ParsedMacroArg = Option<(Script, ArithmeticExpression)>;

#[derive(Clone)]
pub(super) struct MacroInvocationParser<'src, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    expr_parser: Boxed<'src, 'src, I, (Span, ParsedMacroArg), ExtraWithoutContext<'src>>,
    defined_macro_name_parser: Boxed<'src, 'src, I, MacroDefinition, ExtraWithoutContext<'src>>,
}

impl<'src, I> MacroInvocationParser<'src, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    pub(super) fn new(
        expr_parser: Boxed<'src, 'src, I, (Span, ParsedMacroArg), ExtraWithoutContext<'src>>,
        defined_macro_name_parser: Boxed<'src, 'src, I, MacroDefinition, ExtraWithoutContext<'src>>,
    ) -> Self {
        Self {
            expr_parser,
            defined_macro_name_parser,
        }
    }
}

impl<'src, I> Default for MacroInvocationParser<'src, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    fn default() -> Self {
        Self {
            expr_parser: arithmetic_expression_in_any_script_allowing_spaces()
                .or_not()
                .map_with(|got, extra| match got {
                    Some((span, script, expr)) => (span, Some((script, expr))),
                    None => (extra.span(), None),
                })
                .boxed(),
            defined_macro_name_parser: defined_macro_name().boxed(),
        }
    }
}

impl<'src, I> ExtParser<'src, I, MacroInvocation, ExtraWithoutContext<'src>>
    for MacroInvocationParser<'src, I>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    fn parse(
        &self,
        inp: &mut InputRef<'src, '_, I, ExtraWithoutContext<'src>>,
    ) -> Result<
        MacroInvocation,
        <Full<Rich<'src, Tok>, State<'src>, ()> as ParserExtra<'src, I>>::Error,
    > {
        let before = inp.cursor();
        let macro_def: MacroDefinition = inp.parse(&self.defined_macro_name_parser)?;
        let param_defs: Vec<MacroParameter> = match macro_def.params {
            MacroDummyParameters::Zero(ref expected) => {
                if let Some(got) = inp.next_maybe().as_deref() {
                    if got == expected {
                        Vec::new()
                    } else {
                        return Err(Rich::custom(
                            inp.span_since(&before),
                            format!(
                                "expected macro name {} to be followed a terminator {} but got {}",
                                macro_def.name, expected, got
                            ),
                        ));
                    }
                } else {
                    return Err(Rich::custom(
                        inp.span_since(&before),
                        format!(
                            "expected macro name {} to be followed a terminator {}",
                            macro_def.name, expected
                        ),
                    ));
                }
            }
            MacroDummyParameters::OneOrMore(ref params) => params.clone(),
        };
        let mut param_values: MacroParameterBindings = Default::default();
        for param_def in param_defs {
            let before = inp.cursor();
            if let Some(got) = inp.next_maybe().as_deref() {
                let span = inp.span_since(&before);
                if got == &param_def.preceding_terminator {
                    match inp.parse(&self.expr_parser)? {
                        (span, Some((script, expr))) => {
                            param_values.insert(
                                param_def.name,
                                span,
                                Some(MacroParameterValue::Value(script, expr)),
                            );
                        }
                        (span, None) => {
                            // Record the fact that this parameter was missing.
                            param_values.insert(param_def.name, span, None);
                        }
                    }
                } else {
                    return Err(Rich::custom(
                        span,
                        format!(
                            "in invocation of macro {}, expected macro terminator {} before parameter {} but got {}",
                            macro_def.name, param_def.preceding_terminator, param_def.name, got
                        ),
                    ));
                }
            } else {
                let span = inp.span_since(&before);
                return Err(Rich::custom(
                    span,
                    format!(
                        "in invocation of macro {}, expected macro terminator {} before parameter {}",
                        macro_def.name, param_def.preceding_terminator, param_def.name
                    ),
                ));
            }
        }
        Ok(MacroInvocation {
            macro_def,
            param_values,
        })
    }
}

pub(super) fn defined_macro_name<'src, I>()
-> impl Parser<'src, I, MacroDefinition, ExtraWithoutContext<'src>>
where
    I: Input<'src, Token = Tok, Span = Span> + ValueInput<'src>,
{
    fn mapping<'a>(
        name: &SymbolName,
        state: &State,
        span: Span,
    ) -> Result<MacroDefinition, chumsky::error::Rich<'a, Tok>> {
        match state.get_macro_definition(name) {
            None => Err(Rich::custom(span, format!("unknown macro {name}"))),
            Some(macro_def) => Ok(macro_def.clone()),
        }
    }

    symex::parse_symex(SymexSyllableRule::OneOnly, Script::Normal).try_map_with(|name, extra| {
        let span: Span = extra.span();
        let state: &State = extra.state();
        mapping(&name, state, span)
    })
}

#[cfg(test)]
mod tests {
    use chumsky::prelude::SimpleSpan;

    use crate::collections::OneOrMore;
    use base::{charset::Script, u36};

    use super::{
        super::{
            super::{
                ast::{
                    ArithmeticExpression, Atom, CommaDelimitedFragment, ConfigValue, EqualityValue,
                    HoldBit, InstructionFragment, InstructionSequence, LiteralValue,
                    SymbolOrLiteral, Tag, TaggedProgramInstruction, UntaggedProgramInstruction,
                },
                manuscript::{
                    MacroBody, MacroBodyLine, MacroDefinition, MacroDummyParameters,
                    MacroInvocation, MacroParameter, MacroParameterBindings, MacroParameterValue,
                    ManuscriptBlock, SourceFile,
                },
                state::State,
                symbol::SymbolName,
                symtab::{ExplicitDefinition, ExplicitSymbolTable},
            },
            grammar,
            lexer::Token,
            tests::{
                assignment_of_literal, atom_to_fragment, no_state_setup, notags,
                parse_source_file_successfully, parse_successfully_with, parse_with, span,
            },
        },
        macro_body, macro_definition, macro_definition_dummy_parameter,
        macro_definition_dummy_parameters, macro_invocation,
    };

    #[test]
    fn test_macro_body_accepts_two_lines() {
        let g = grammar();
        parse_successfully_with("SOMETHING\nWORLD\n", macro_body(&g), no_state_setup);
    }

    #[test]
    fn test_macro_body_accepts_empty_macro_body() {
        let input = "";
        let g = grammar();
        let result = parse_with(input, macro_body(&g), no_state_setup);
        assert!(
            result.is_ok(),
            "expected input '{input}' to be accepted but got {result:?}"
        );
    }

    #[cfg(test)]
    fn check_macro_body_symex_span(input: &str, span_expected: SimpleSpan) {
        dbg!(input, &span_expected);
        let g = grammar();
        let parsed_body = parse_successfully_with(input, macro_body(&g), no_state_setup);
        let lines = parsed_body.parsed_body_lines();
        dbg!(&lines);
        match &lines[0] {
            MacroBodyLine::Instruction(TaggedProgramInstruction { span: the_span, .. }) => {
                assert_eq!(the_span, &span_expected, "incorrect span");
            }
            other => {
                panic!("expected first line to be an instruction, got {other:?}");
            }
        }
    }

    #[test]
    fn test_macro_body_generates_symexes_whose_span_does_not_include_newline() {
        check_macro_body_symex_span("R\n", span(0..1));
    }

    #[test]
    fn test_macro_body_generates_symexes_whose_span_does_not_include_comments() {
        check_macro_body_symex_span("W ** this is a comment\n", span(0..1));
    }

    #[test]
    fn test_macro_arg() {
        assert_eq!(
            parse_successfully_with(
                "@hand@A01",
                macro_definition_dummy_parameter(),
                no_state_setup
            ),
            MacroParameter {
                name: SymbolName::from("A01".to_string()),
                span: span(0..9),
                preceding_terminator: Token::Hand(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with(
                "@comma@A02",
                macro_definition_dummy_parameter(),
                no_state_setup
            ),
            MacroParameter {
                name: SymbolName::from("A02".to_string()),
                span: span(0..10),
                preceding_terminator: Token::Comma(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("=A03", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A03".to_string()),
                span: span(0..4),
                preceding_terminator: Token::Equals(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with(
                "@arr@A04",
                macro_definition_dummy_parameter(),
                no_state_setup
            ),
            MacroParameter {
                name: SymbolName::from("A04".to_string()),
                span: span(0..8),
                preceding_terminator: Token::Arrow(Script::Normal),
            }
        );

        assert_eq!(
            // Alternative form for convenience (and consistency with
            // what we allow for tags).
            parse_successfully_with("->A04", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A04".to_string()),
                span: span(0..5),
                preceding_terminator: Token::Arrow(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("|A05", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A05".to_string()),
                span: span(0..4),
                preceding_terminator: Token::Pipe(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("⊃A06", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A06".to_string()),
                span: span(0..6),
                preceding_terminator: Token::ProperSuperset(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("≡A07", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A07".to_string()),
                span: span(0..6),
                preceding_terminator: Token::IdenticalTo(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with(
                "@hamb@A07",
                macro_definition_dummy_parameter(),
                no_state_setup
            ),
            MacroParameter {
                name: SymbolName::from("A07".to_string()),
                span: span(0..9),
                preceding_terminator: Token::IdenticalTo(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("~A08", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A08".to_string()),
                span: span(0..4),
                preceding_terminator: Token::Tilde(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("<A09", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A09".to_string()),
                span: span(0..4),
                preceding_terminator: Token::LessThan(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with(">A10", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A10".to_string()),
                span: span(0..4),
                preceding_terminator: Token::GreaterThan(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("∩A11", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A11".to_string()),
                span: span(0..6),
                preceding_terminator: Token::Intersection(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("∪A12", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A12".to_string()),
                span: span(0..6),
                preceding_terminator: Token::Union(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("/A13", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A13".to_string()),
                span: span(0..4),
                preceding_terminator: Token::Solidus(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("×A14", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A14".to_string()),
                span: span(0..5),
                preceding_terminator: Token::Times(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("∨A15", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A15".to_string()),
                span: span(0..6),
                preceding_terminator: Token::LogicalOr(Script::Normal),
            }
        );

        assert_eq!(
            parse_successfully_with("∧A16", macro_definition_dummy_parameter(), no_state_setup),
            MacroParameter {
                name: SymbolName::from("A16".to_string()),
                span: span(0..6),
                preceding_terminator: Token::LogicalAnd(Script::Normal),
            }
        );
    }

    #[test]
    fn test_macro_args() {
        assert_eq!(
            parse_successfully_with(
                "=X@hand@YZ@arr@P",
                macro_definition_dummy_parameters(),
                no_state_setup
            ),
            MacroDummyParameters::OneOrMore(vec![
                MacroParameter {
                    name: SymbolName::from("X".to_string()),
                    span: span(0..2),
                    preceding_terminator: Token::Equals(Script::Normal),
                },
                MacroParameter {
                    name: SymbolName::from("YZ".to_string()),
                    span: span(2..10),
                    preceding_terminator: Token::Hand(Script::Normal),
                },
                MacroParameter {
                    name: SymbolName::from("P".to_string()),
                    span: span(10..16),
                    preceding_terminator: Token::Arrow(Script::Normal),
                },
            ])
        );
    }

    #[test]
    fn test_macro_definition_with_empty_body() {
        // TBD: where in a macro definition are comments allowed?
        let input = concat!("☛☛DEF MYMACRO≡\n", "☛☛EMD"); // deliberately no terminating newline, see comment in macro_definition().
        dbg!(&input[21..]);
        let got = parse_successfully_with(input, macro_definition(), no_state_setup);
        let expected = MacroDefinition {
            name: SymbolName::from("MYMACRO".to_string()),
            params: MacroDummyParameters::Zero(Token::IdenticalTo(Script::Normal)),
            body: MacroBody::default(),
            span: span(0..30),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_macro_definition_with_trivial_body() {
        let input = concat!(
            "☛☛DEF JUST|Q\n",
            // This macro definition has a one-line body.
            "Q ** This is the only line in the body.\n",
            "☛☛EMD" // deliberately no terminating newline, see comment in macro_definition().
        );
        dbg!(&input[0..57]);
        dbg!(&input[0..66]);
        let got = parse_successfully_with(input, macro_definition(), no_state_setup);
        let expected = MacroDefinition {
            name: SymbolName::from("JUST".to_string()),
            params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                name: SymbolName::from("Q".to_string()),
                span: span(14..16),
                preceding_terminator: Token::Pipe(Script::Normal),
            }]),
            body: vec![MacroBodyLine::Instruction(
                TaggedProgramInstruction::single(
                    notags(),
                    HoldBit::Unspecified,
                    span(17..18),
                    span(17..18),
                    InstructionFragment::Arithmetic(ArithmeticExpression::from(
                        Atom::SymbolOrLiteral(SymbolOrLiteral::Symbol(
                            Script::Normal,
                            SymbolName::from("Q"),
                            span(17..18),
                        )),
                    )),
                ),
            )]
            .into(),
            span: span(0..66),
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_macro_definition_as_entire_source_file() {
        let got = parse_source_file_successfully("☛☛DEF JUST|Q\nQ\n☛☛EMD\n");
        let expected = SourceFile {
            blocks: Default::default(),            // empty
            global_equalities: Default::default(), // no equalities
            macros: [(
                SymbolName::from("JUST".to_string()),
                MacroDefinition {
                    name: SymbolName {
                        canonical: "JUST".to_string(),
                    },
                    params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                        name: SymbolName {
                            canonical: "Q".to_string(),
                        },
                        span: span(14..16),
                        preceding_terminator: Token::Pipe(Script::Normal),
                    }]),
                    body: vec![MacroBodyLine::Instruction(
                        TaggedProgramInstruction::single(
                            notags(),
                            HoldBit::Unspecified,
                            span(17..18),
                            span(17..18),
                            InstructionFragment::Arithmetic(ArithmeticExpression::from(
                                Atom::from((span(17..18), Script::Normal, SymbolName::from("Q"))),
                            )),
                        ),
                    )]
                    .into(),
                    span: span(0..28),
                },
            )]
            .into_iter()
            .collect(),
            punch: None,
        };
        assert_eq!(got, expected);
    }

    #[test]
    fn test_parse_macro_invocation() {
        let macro_definition_foo = MacroDefinition {
            name: SymbolName::from("FOO"),
            params: MacroDummyParameters::OneOrMore(vec![MacroParameter {
                name: SymbolName::from("A1"),
                span: span(10..12),
                preceding_terminator: Token::Tilde(Script::Normal),
            }]),
            body: vec![MacroBodyLine::Instruction(TaggedProgramInstruction {
                span: span(0..24),
                tags: notags(),
                instruction: UntaggedProgramInstruction::from(OneOrMore::new(
                    CommaDelimitedFragment {
                        leading_commas: None,
                        holdbit: HoldBit::Unspecified,
                        span: span(16..20),
                        fragment: InstructionFragment::Config(ConfigValue {
                            already_superscript: false,
                            expr: ArithmeticExpression::from(Atom::from((
                                span(4..5),
                                Script::Normal,
                                SymbolName::from("X"),
                            ))),
                        }),
                        trailing_commas: None,
                    },
                )),
            })]
            .into(),
            span: span(20..40),
        };
        let set_up_macro_definition = |state: &mut State| {
            state.define_macro(macro_definition_foo.clone());
        };
        let got = parse_successfully_with("FOO~X", macro_invocation(), set_up_macro_definition);

        let mut bindings: MacroParameterBindings = Default::default();
        bindings.insert(
            SymbolName::from("A1"),
            span(4..5),
            Some(MacroParameterValue::Value(
                Script::Normal,
                ArithmeticExpression::from(Atom::from((
                    span(4..5),
                    Script::Normal,
                    SymbolName::from("X"),
                ))),
            )),
        );

        assert_eq!(
            got,
            MacroInvocation {
                macro_def: macro_definition_foo,
                param_values: bindings,
            }
        );
    }

    #[test]
    fn test_parse_macro_invocation_with_equality() {
        let got = parse_source_file_successfully(concat!(
            "☛☛DEF MYMACRO≡\n",
            "     X = 1\n",
            // Although this tag ends up in the program twice,
            // this is valid since each the tags in the two macro
            // expansions are separate.
            " T-> 2\n",
            "☛☛EMD",
            "\n",
            // We expand the macro twice.
            "MYMACRO≡\n",
            "MYMACRO≡\n",
        ));

        let symtab: ExplicitSymbolTable = {
            let mut st = ExplicitSymbolTable::default();
            st.define(
                SymbolName::from("X"),
                ExplicitDefinition::Equality(EqualityValue::from((
                    span(30..31),
                    UntaggedProgramInstruction::from(OneOrMore::new(CommaDelimitedFragment {
                        leading_commas: None,
                        holdbit: HoldBit::Unspecified,
                        span: span(30..31),
                        fragment: atom_to_fragment(Atom::from(LiteralValue::from((
                            span(30..31),
                            Script::Normal,
                            u36!(1),
                        )))),
                        trailing_commas: None,
                    })),
                ))),
            )
            .expect("assignment should be valid");
            st
        };

        let the_instruction = TaggedProgramInstruction::single(
            vec![Tag {
                name: SymbolName::from("T"),
                span: span(33..34),
            }],
            HoldBit::Unspecified,
            span(33..38),
            span(37..38),
            InstructionFragment::from((span(37..38), Script::Normal, u36!(2))),
        );

        let expected = SourceFile {
            blocks: vec![ManuscriptBlock {
                origin: None,
                sequences: vec![
                    // The first macro expansion
                    InstructionSequence {
                        local_symbols: Some(symtab.clone()),
                        instructions: vec![the_instruction.clone()],
                    },
                    // The second macro expansion
                    InstructionSequence {
                        local_symbols: Some(symtab.clone()),
                        instructions: vec![the_instruction.clone()],
                    },
                ],
            }],
            // There are no global equalities since the only equality
            // is local to the macro body.
            global_equalities: Default::default(),
            macros: [(
                SymbolName::from("MYMACRO"),
                MacroDefinition {
                    name: SymbolName::from("MYMACRO"),
                    params: MacroDummyParameters::Zero(Token::IdenticalTo(Script::Normal)),
                    body: vec![
                        MacroBodyLine::Equality(assignment_of_literal(
                            "X",
                            span(26..31),
                            LiteralValue::from((span(30..31), Script::Normal, u36!(1))),
                        )),
                        MacroBodyLine::Instruction(the_instruction.clone()),
                    ]
                    .into(),
                    span: span(0..48),
                },
            )]
            .into_iter()
            .collect(),
            punch: None,
        };

        assert_eq!(got, expected,);
    }

    #[test]
    fn test_parse_macro_used_before_defined() {
        // In this test we do not actually invoke OUTER because
        // recursive macros are not yet supported.
        parse_source_file_successfully(concat!(
            "☛☛DEF INNER≡P\n",
            "     P+2\n",
            "☛☛EMD\n",
            "☛☛DEF OUTER≡P\n",
            "     INNER≡(P+1)\n",
            "☛☛EMD\n",
        ));
    }

    #[test]
    fn test_parse_macro_defined_before_used() {
        // In this test we do not actually invoke OUTER because
        // recursive macros are not yet supported.
        parse_source_file_successfully(concat!(
            "☛☛DEF OUTER≡P\n",
            "     INNER≡(P+1)\n",
            "☛☛EMD\n",
            "☛☛DEF INNER≡P\n",
            "     P+2\n",
            "☛☛EMD\n",
        ));
    }
}
