//! The `base` crate defines the TX2-related things which are useful
//! in both a simulator and other associated tools.  The idea is that
//! if you want to write an assembler, it would depend on the base
//! crate but would not need to depend on the simulator library
//! itself.

mod onescomplement;
mod types;

pub mod instruction;
pub mod prelude;
pub mod subword;
