use std::fmt::Display;

use super::ast::Origin;
use super::span::Span;
use super::span::{extract_prefix, extract_span};
use super::symtab::FinalSymbolTable;
use super::types::RcWordSource;
use base::prelude::*;

#[derive(Debug, Default)]
pub(crate) struct Listing {
    final_symbols: FinalSymbolTable,
    output: Vec<ListingLine>,
    rc_block: Vec<ListingLine>,
}

impl Listing {
    pub(super) fn set_final_symbols(&mut self, final_symbols: FinalSymbolTable) {
        self.final_symbols = final_symbols;
    }

    pub(super) fn push_line(&mut self, line: ListingLine) {
        self.output.push(line)
    }

    pub(super) fn push_rc_line(&mut self, line: ListingLine) {
        self.rc_block.push(line)
    }

    fn format_symbol_table(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.final_symbols)
    }
}

#[derive(Debug)]
pub(super) struct ListingLine {
    pub(super) origin: Option<Origin>,
    pub(super) span: Option<Span>,
    pub(super) rc_source: Option<RcWordSource>,
    pub(super) content: Option<(Address, Unsigned36Bit)>,
}

struct ListingLineWithBody<'a> {
    line: &'a ListingLine,
    body: &'a str,
}

fn write_address(f: &mut std::fmt::Formatter<'_>, addr: &Address) -> std::fmt::Result {
    let addr_value: Unsigned18Bit = (*addr).into();
    if addr_value & 0o7 == 0 {
        write!(f, "{addr_value:>06o}")
    } else {
        write!(f, "   {:>03o}", addr_value & 0o777)
    }
}

impl Display for ListingLineWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(origin) = self.line.origin.as_ref() {
            writeln!(f, "{origin}| ** origin")?;
        }

        match self.line.rc_source.as_ref() {
            Some(RcWordSource::DefaultAssignment(_, name)) => {
                write!(f, "{name:10}-> ")?;
            }
            Some(RcWordSource::Braces(_)) | Some(RcWordSource::PipeConstruct(_)) | None => {
                write!(f, "{:13}", "")?;
            }
        }

        let source_span_to_print: Option<Span> = match self.line.span.as_ref() {
            Some(span) => Some(*span),
            None => match self.line.rc_source.as_ref() {
                Some(RcWordSource::Braces(span)) | Some(RcWordSource::PipeConstruct(span)) => {
                    Some(*span)
                }
                _ => None,
            },
        };

        if let Some(span) = source_span_to_print {
            let s = extract_span(self.body, &span).trim();
            let prefix = extract_prefix(self.body, span.start);
            write!(f, "{prefix}{s:54}")?;
        } else if matches!(
            &self.line.rc_source,
            Some(RcWordSource::DefaultAssignment(_, _))
        ) {
            write!(f, "{:<54}", 0)?;
        }

        if let Some((address, word)) = self.line.content.as_ref() {
            let (left, right) = split_halves(*word);
            write!(f, " |{left:06} {right:06}| ")?;
            write_address(f, address)?;
        }
        Ok(())
    }
}

pub(super) struct ListingWithBody<'a> {
    pub(super) listing: &'a Listing,
    pub(super) body: &'a str,
}

impl Display for ListingWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_listing_line(
            f: &mut std::fmt::Formatter<'_>,
            body: &str,
            line: &ListingLine,
        ) -> std::fmt::Result {
            writeln!(f, "{}", &ListingLineWithBody { line, body })
        }

        writeln!(f, "Symbol Table:")?;
        self.listing.format_symbol_table(f)?;
        writeln!(f)?;

        writeln!(f, "Directive:")?;
        for line in self.listing.output.iter() {
            write_listing_line(f, self.body, line)?;
        }

        if !self.listing.rc_block.is_empty() {
            writeln!(f, "☛☛RC")?;
            for line in self.listing.rc_block.iter() {
                write_listing_line(f, self.body, line)?;
            }
        }
        Ok(())
    }
}
