//! This module decodes instructions and emulates the arithmetic unit,
//! the exchange unit, memory and the CPU side of the I/O system.
//!
//! All the work is done in non-blocking function calls into this library.
#![crate_name = "cpu"]
#![deny(unreachable_pub)]
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

pub use alarm::{Alarm, AlarmDetails, AlarmKind, UnmaskedAlarm};
pub use alarmunit::AlarmStatus;
pub use context::Context;
pub use control::{ControlRegisters, ControlUnit, PanicOnUnmaskedAlarm, ResetMode, RunMode};
pub use event::*;
pub use io::{DeviceManager, ExtendedUnitState, InputFlagRaised, set_up_peripherals};
pub use memory::{MemoryConfiguration, MemoryUnit};
pub use tx2::Tx2;
pub use types::*;

pub const PETR: base::prelude::Unsigned6Bit = base::prelude::u6!(0o52);
