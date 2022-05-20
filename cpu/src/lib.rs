//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]

mod alarm;
mod control;
mod event;
mod exchanger;
mod io;
mod memory;
mod tx2;
mod types;

pub use alarm::{Alarm, UnmaskedAlarm};
pub use control::{ControlUnit, PanicOnUnmaskedAlarm, ResetMode, RunMode};
pub use event::*;
pub use io::{set_up_peripherals, DeviceManager};
pub use memory::{MemoryConfiguration, MemoryUnit};
pub use tx2::Tx2;
pub use types::*;

pub const PETR: base::prelude::Unsigned6Bit = base::prelude::u6!(0o52);
