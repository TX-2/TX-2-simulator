//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]
#![deny(unsafe_code)]
#![deny(unused_crate_dependencies)]

mod alarm;
mod alarmunit;
mod changelog;
mod context;
mod control;
mod event;
mod exchanger;
mod io;
mod memory;
mod tx2;
mod types;

pub use alarm::{Alarm, AlarmKind, UnmaskedAlarm};
pub use alarmunit::AlarmStatus;
pub use context::Context;
pub use control::{ControlUnit, PanicOnUnmaskedAlarm, ResetMode, RunMode};
pub use event::*;
pub use io::{set_up_peripherals, DeviceManager, ExtendedUnitState};
pub use memory::{MemoryConfiguration, MemoryUnit};
pub use tx2::Tx2;
pub use types::*;

pub const PETR: base::prelude::Unsigned6Bit = base::prelude::u6!(0o52);
