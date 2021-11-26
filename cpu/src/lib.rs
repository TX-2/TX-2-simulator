//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.

mod alarm;
mod control;
mod exchanger;
mod memory;
mod memorymap;

pub use alarm::Alarm;
pub use control::{ControlUnit, ResetMode};
pub use memory::{MemoryConfiguration, MemoryUnit};
