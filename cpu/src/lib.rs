//! This crate decodes instructions and emulates the arithmetic unit,
//! the exchange unit, memory and the CPU side of the I/O system.
//!
//! All the work is done in non-blocking function calls into this library.
//!
//! The modules within this crate do not directly map to the elements
//! of the TX-2 machine.
//!
//!
//! | TX-2 Element    | Feature | Implementation |
//! |--- ------------ | ------  | -------------  |
//! | Control Element | Start/Stop control, CODABO, STARTOVER, Sequencing the stages of instructions | [control]|
//! | Control Element | Alarms  | [alarmunit]|
//! | In/Out Element  | All     | [io]|
//! | Program Element | Sequence flags, Index register storage, Instruction decoding, Instruction, executrion, Deferred addressing| [control]|
//! | Program Element | Sequence selection and switching | [control]|
//! | Program Element | Registers N, P, Q, K | [control]|
//! | Program Element | Configuration memory | [control]|
//! | Program Element | Jumps | [control]|
//! | Arithmetic Element | Register A, B, C, D, Arithmetic operations,  | [control] |
//! | Arithmetic Element | Registers Y and Z  |  Not yet implemented |
//! | Exchange Element | Load/store process | [exchanger] |
//! | Exchange Element | Register E |  [exchanger] |
//! | Exchange Element | Register M |  [memory] |
//! | Exchange Element | Quarter activity, subword form, sign extension  |  [exchanger] |
//! | In/Out Element | Connecting/disconnecting peripherals, raising the flag of sequences for which I/O is ready | [io]|
//! | Memory Element | Memory storage | [exchanger](crate::memory) |
//! | Console           | Toggle Start Point Register  |  [control::ControlUnit] |
//!
#![crate_name = "cpu"]
#![deny(unreachable_pub)]
#![deny(unsafe_code)]
#![deny(unused_crate_dependencies)]
#![warn(clippy::must_use_candidate)]
#![warn(clippy::manual_string_new)]
#![warn(clippy::semicolon_if_nothing_returned)]
//#![warn(clippy::pedantic)]
#![allow(clippy::unreadable_literal)] // fix later, there are many
#![warn(clippy::similar_names)] // included in `pedantic`
#![warn(clippy::if_not_else)] // included in `pedantic`
#![warn(clippy::items_after_statements)] // included in `pedantic`
#![warn(clippy::explicit_iter_loop)] // included in `pedantic`
#![warn(clippy::doc_markdown)] // included in `pedantic`
#![allow(rustdoc::private_intra_doc_links)]

mod alarm;
mod alarmunit;
mod bugreport;
mod changelog;
mod context;
mod control;
mod diagnostics;
mod event;
mod exchanger;
mod io;
mod memory;
mod tx2;
mod types;

pub use alarm::{Alarm, AlarmDetails, AlarmKind, UnmaskedAlarm};
pub use alarmunit::AlarmStatus;
pub use bugreport::bug_report_url;
pub use context::Context;
pub use control::{ControlRegisters, ControlUnit, PanicOnUnmaskedAlarm, ResetMode, RunMode};
pub use event::*;
pub use io::{
    DeviceManager, ExtendedConnectedUnitStatus, ExtendedUnitState, InputFlagRaised,
    set_up_peripherals,
};
pub use memory::{MemoryConfiguration, MemoryUnit};
pub use tx2::Tx2;
pub use types::*;

pub const PETR: base::prelude::Unsigned6Bit = base::prelude::u6!(0o52);
