//! This module decodes instructions and emulates the arithmetic unit
//! and the exchange unit.
#![crate_name = "cpu"]

use std::time::Duration;

use tracing::{event, Level};

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

pub fn run_until_alarm(
    control: &mut ControlUnit,
    mem: &mut MemoryUnit,
    clk: &mut BasicClock,
) -> Result<(), Alarm> {
    let mut elapsed_ns: u64 = 0;
    let mut sleeper = MinimalSleeper::new(Duration::from_millis(2));
    loop {
        control.poll_hardware(&clk.now())?; // check for I/O alarms, flag changes.
        if !control.fetch_instruction(mem)? {
            break;
        }
        elapsed_ns += match control.execute_instruction(&clk.now(), mem) {
            Err(e) => {
                event!(Level::INFO, "Alarm raised after {}ns", elapsed_ns);
                return Err(e);
            }
            Ok(ns) => {
                let delay = clk.consume(&Duration::from_nanos(ns));
                if !delay.is_zero() {
                    sleeper.sleep(&delay);
                }
                ns
            }
        };
    }
    event!(Level::INFO, "Stopped after {}ns", elapsed_ns);
    Ok(())
}
