use std::fmt::Display;

use super::ast::Origin;
use super::ast::TaggedProgramInstruction;
use super::span::extract_span;
use super::symtab::FinalSymbolTable;
use base::prelude::*;

#[derive(Debug, Default)]
pub(crate) struct Listing {
    final_symbols: FinalSymbolTable,
    output: Vec<ListingLine>,
}

impl Listing {
    pub(super) fn set_final_symbols(&mut self, final_symbols: FinalSymbolTable) {
        self.final_symbols = final_symbols;
    }

    pub(super) fn push_line(&mut self, line: ListingLine) {
        self.output.push(line)
    }

    fn format_symbol_table(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.final_symbols)
    }
}

#[derive(Debug)]
pub(super) enum ListingLine {
    Origin(Origin),
    Instruction {
        address: Address,
        instruction: TaggedProgramInstruction,
        binary: Unsigned36Bit,
    },
}

struct ListingLineWithBody<'a> {
    line: &'a ListingLine,
    body: &'a str,
}

impl Display for ListingLineWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.line {
            ListingLine::Origin(origin) => {
                write!(f, "{origin}|")
            }
            ListingLine::Instruction {
                address,
                instruction,
                binary,
            } => {
                let displayed_tag: Option<&str> = instruction
                    .tag
                    .as_ref()
                    .map(|t| extract_span(self.body, &t.span));
                match displayed_tag {
                    Some(t) => {
                        write!(f, "{t:10}->")?;
                    }
                    None => {
                        const EMPTY: &str = "";
                        write!(f, "{EMPTY:12}")?;
                    }
                }
                let displayed_instruction: &str =
                    extract_span(self.body, &instruction.span()).trim();
                let (left, right) = split_halves(*binary);
                write!(f, "{displayed_instruction:30}  |{left:06} {right:06}| ")?;

                let addr_value: Unsigned18Bit = (*address).into();
                if addr_value & 0o7 == 0 {
                    write!(f, "{addr_value:>06o}")
                } else {
                    write!(f, "   {:>03o}", addr_value & 0o777)
                }
            }
        }
    }
}

pub(super) struct ListingWithBody<'a> {
    pub(super) listing: &'a Listing,
    pub(super) body: &'a str,
}

impl Display for ListingWithBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Symbol Table:")?;
        self.listing.format_symbol_table(f)?;
        writeln!(f)?;

        writeln!(f, "Directive:")?;
        for line in self.listing.output.iter() {
            writeln!(
                f,
                "{}",
                &ListingLineWithBody {
                    line,
                    body: self.body,
                }
            )?;
        }
        Ok(())
    }
}
