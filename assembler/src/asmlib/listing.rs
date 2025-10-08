use std::fmt::Display;

use super::memorymap::{RcWordKind, RcWordSource};
use super::source::Source;
use super::span::Span;
use super::symtab::FinalSymbolTable;
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
        self.output.push(line);
    }

    pub(super) fn push_rc_line(&mut self, line: ListingLine) {
        self.rc_block.push(line);
    }

    fn format_symbol_table(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.final_symbols)
    }
}

#[derive(Debug)]
pub(super) struct ListingLine {
    pub(super) span: Option<Span>,
    pub(super) rc_source: Option<RcWordSource>,
    pub(super) content: Option<(Address, Unsigned36Bit)>,
}

struct ListingLineWithBody<'a, 'b> {
    line: &'a ListingLine,
    body: &'b Source<'a>,
}

fn write_address(f: &mut std::fmt::Formatter<'_>, addr: Address) -> std::fmt::Result {
    let addr_value: Unsigned18Bit = addr.into();
    if addr_value & 0o7 == 0 {
        write!(f, "{addr_value:>06o}")
    } else {
        write!(f, "   {:>03o}", addr_value & 0o777)
    }
}

impl Display for ListingLineWithBody<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let source_span_to_print: Option<Span> = match self.line.span.as_ref() {
            Some(span) => Some(*span),
            None => self.line.rc_source.as_ref().map(|source| source.span),
        };

        if let Some(span) = source_span_to_print {
            let s = self.body.extract(span.start..span.end).trim();
            let prefix = self.body.extract_prefix(span.start);
            write!(f, "{prefix}{s:54}")?;
        } else if matches!(
            &self.line.rc_source,
            Some(RcWordSource {
                kind: RcWordKind::DefaultAssignment,
                ..
            })
        ) {
            write!(f, "{:<54}", 0)?;
        }

        if let Some((address, word)) = self.line.content.as_ref() {
            let (left, right) = split_halves(*word);
            write!(f, " |{left:06} {right:06}| ")?;
            write_address(f, *address)?;
        }
        Ok(())
    }
}

pub(super) struct ListingWithBody<'a, 'b> {
    pub(super) listing: &'a Listing,
    pub(super) body: &'b Source<'a>,
}

impl Display for ListingWithBody<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_listing_line(
            f: &mut std::fmt::Formatter<'_>,
            body: &Source,
            line: &ListingLine,
        ) -> std::fmt::Result {
            writeln!(f, "{}", &ListingLineWithBody { line, body })
        }

        writeln!(f, "Symbol Table:")?;
        self.listing.format_symbol_table(f)?;
        writeln!(f)?;

        writeln!(f, "Directive:")?;
        for line in &self.listing.output {
            write_listing_line(f, self.body, line)?;
        }

        if !self.listing.rc_block.is_empty() {
            writeln!(f, "☛☛RC")?;
            for line in &self.listing.rc_block {
                write_listing_line(f, self.body, line)?;
            }
        }
        Ok(())
    }
}
