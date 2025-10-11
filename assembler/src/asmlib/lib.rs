//! Assembler for the TX-2.
//!
//! Accepts symbolic assembly source code for the TX-2.  Follows the
//! syntax and behaviour of the TX-2's M4 assembler written by Larry
//! Roberts.
//!
//! There are a number of differences between this assembler and M4.  These are:
//!
//! - This assembler's input is a Unicode text file, while M4's input
//!   was a tape (or magnetic tape input) containing Lincoln Writer codes.
//!   This has some consequences for how the input is represented (among
//!   other reasons because the Lincoln Writer supported some superscript
//!   and subscript characters which are not in Unicode).
//! - M4's input includes editing commands; these are not needed on
//!   modern systems, since they support files and editors which are
//!   independent of the assembler.
//! - M4 produced output directly on a paper tape; this assmebler
//!   produces a tape image file (containing the same data).
//! - Some features, notably support for local tag scope inside macro
//!   bodies, are not yet implemented.
//! - Tab characters are not supported in the input.
//! - This assembler produces diagnositics for some kinds of erroneous
//!   input that M4 accepted (see below).
//!
//! # Diagnostics
//!
//! This assembler produces diagnostics giving the line number (and
//! often, the approximate column number) of errors.
//!
//! The M4 assembler accepted circular symbol definitions (for origins
//! for example, see XXX) but this assembler detects this and generates
//! an error message.
//!
//! There may be some cases in which M4 generated an error but were we
//! either do not, or where we lack a test ensuring that the error
//! message is correctly generated;
//! <https://github.com/TX-2/TX-2-simulator/issues/159> enumerates
//! these.
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
#![allow(clippy::too_many_lines)] // fix later
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
