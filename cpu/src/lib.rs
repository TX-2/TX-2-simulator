//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]

mod alarm;
mod clock;
mod control;
mod exchanger;
pub mod io;
mod memory;

pub use alarm::Alarm;
pub use clock::{BasicClock, Clock, MinimalSleeper};
pub use control::{ControlUnit, ResetMode};
pub use memory::{MemoryConfiguration, MemoryUnit};
