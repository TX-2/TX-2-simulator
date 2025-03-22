#![deny(unreachable_pub)]
#![deny(unsafe_code)]

mod ast;
mod driver;
mod eval;
mod glyph;
mod lexer;
mod parser;
mod state;
mod symbol;
mod symtab;
mod types;

pub use driver::*;
pub use types::Fail;
