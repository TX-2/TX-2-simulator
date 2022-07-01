#![deny(unreachable_pub)]
#![deny(unsafe_code)]

mod driver;
mod ek;
mod parser;
mod state;
mod types;

#[cfg(test)]
mod tests;

pub use driver::*;
pub use types::Fail;
