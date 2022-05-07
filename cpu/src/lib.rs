//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]

use std::time::Duration;

mod alarm;
mod clock;
mod control;
mod exchanger;
pub mod io;
mod memory;

pub use alarm::Alarm;
pub use clock::{BasicClock, Clock, MinimalSleeper};
pub use control::{ControlUnit, PanicOnUnmaskedAlarm, ResetMode, RunMode};
pub use memory::{MemoryConfiguration, MemoryUnit};

pub fn time_passes(
    clk: &mut BasicClock,
    sleeper: &mut MinimalSleeper,
    t: &Duration,
    multiplier: Option<f64>,
) {
    clk.consume(t);
    if let Some(m) = multiplier {
        sleeper.sleep(&t.mul_f64(m));
    }
}
