use chumsky::{
    DefaultExpected,
    error::LabelError,
    extension::v1::{Ext, ExtParser},
    input::{Cursor, InputRef},
    prelude::*,
};

use super::lexer::Token;

pub(crate) struct UnparsedMacroDefinitionsParser_;

fn discard_to_eol<'src, 'p, I, E>(inp: &mut InputRef<'src, 'p, I, E>)
where
    I: Input<'src, Token = Token, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    while let Some(t) = inp.next_maybe().as_deref() {
        if t == &Token::Newline {
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
    I: Input<'src, Token = Token, Span = chumsky::span::SimpleSpan>,
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
                    Token::Newline => {
                        // Since we found a newline, we don't want to
                        // call discard_to_eol.
                    }
                    Token::Hand(Normal) => {
                        match inp.next_maybe().as_deref() {
                            None => {
                                return None;
                            }
                            Some(second_tok) => {
                                match second_tok {
                                    Token::Newline => {
                                        // Since we found a newline, we don't
                                        // want to call discard_to_eol.
                                    }
                                    Token::Hand(Normal) => {
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
    I: Input<'src, Token = Token, Span = chumsky::span::SimpleSpan>,
    E: extra::ParserExtra<'src, I>,
{
    use super::Script::Normal;
    loop {
        let Some(before) = advance_to_double_hand(inp) else {
            // There are no more ☛☛
            return Ok(None);
        };
        match inp.next_maybe().as_deref() {
            found @ Some(Token::SymexSyllable(Normal, actual_cmd)) => {
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
    I: Input<'src, Token = Token, Span = chumsky::span::SimpleSpan>,
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
