//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name="cpu"]

mod alarm;
mod control;
mod exchanger;
mod io;
mod memory;

pub use alarm::Alarm;
pub use control::{
    ControlUnit,
    ResetMode
};
pub use control::timing::{
    Clock,
    BasicClock,
    MinimalSleeper,
};
pub use memory::{MemoryConfiguration, MemoryUnit};
