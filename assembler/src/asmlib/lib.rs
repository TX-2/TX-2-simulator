#![deny(unreachable_pub)]
#![deny(unsafe_code)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::manual_string_new)]
#![warn(clippy::semicolon_if_nothing_returned)]
#![warn(clippy::return_self_not_must_use)]
#![warn(clippy::wildcard_imports)]
#![warn(clippy::bool_to_int_with_if)]
#![warn(clippy::clone_on_ref_ptr)]
#![warn(clippy::match_same_arms)]
#![warn(clippy::missing_errors_doc)]
#![warn(clippy::items_after_statements)]
#![warn(clippy::explicit_iter_loop)]
#![warn(clippy::unreadable_literal)]
#![warn(clippy::redundant_closure_for_method_calls)]
#![warn(clippy::pedantic)]
#![allow(clippy::verbose_bit_mask)] // because many of our types don't have trailing_zeros().
#![allow(clippy::enum_glob_use)] // fix later
#![allow(clippy::redundant_else)] // fix later
#![allow(clippy::too_many_lines)] // fix later
#![allow(clippy::similar_names)] // fix later
#![allow(clippy::explicit_into_iter_loop)] // fix later
#![allow(clippy::default_trait_access)] // fix later

mod ast;
mod collections;
mod directive;
mod driver;
mod eval;
mod glyph;
mod lexer;
mod listing;
mod manuscript;
mod memorymap;
mod parser;
mod readerleader;
mod source;
mod span;
mod state;
mod symbol;
mod symtab;
mod types;

pub use driver::*;
pub use readerleader::*;
pub use types::AssemblerFailure;
