//! Lincoln Writer, units 65, 71 (input), 66, 72 (output).
//!
//! A TX-2 unit is always either for input or output, not both
//! (consider for example that the TSD instruction specifies no
//! direction - it is implicit).
//!
///! I am not sure about the timing characteristics of this
///! device.  For now we'll simply assume the output speed is
///! comparable with that of the IBM Selectric typewriter, which is
///! 14.8 characters per second.  This works out at roughly 68
///! milliseconds per character.
use std::fmt::Debug;
use std::time::Duration;

use crate::event::OutputEvent;
use crate::io::{FlagChange, TransferFailed, Unit, UnitStatus};
use crate::types::*;
use base::charset::{lincoln_char_to_described_char, LincolnState};
use base::prelude::*;
use tracing::{event, Level};

const CHAR_TRANSMIT_TIME: Duration = Duration::from_millis(68);
const LATER: Duration = Duration::from_secs(300);

#[derive(Debug)]
pub struct LincolnWriterOutput {
    unit: Unsigned6Bit,
    mode: Unsigned12Bit,
    connected: bool,
    transmit_will_be_finished_at: Option<Duration>,
    // When we implement Lincoln Writer output, we will need to
    // determine a way to share the state information between output
    // and input channels, since this is the way the LW works.  For
    // example, carriage return sets the LW to lower case and normal
    // script, affecting the way input behaves as well as output.
    state: LincolnState,
}

impl LincolnWriterOutput {
    pub fn new(unit: Unsigned6Bit) -> LincolnWriterOutput {
        LincolnWriterOutput {
            unit,
            mode: Unsigned12Bit::ZERO,
            connected: false,
            transmit_will_be_finished_at: None,
            state: LincolnState::default(),
        }
    }
}

impl Unit for LincolnWriterOutput {
    fn poll(&mut self, system_time: &std::time::Duration) -> UnitStatus {
        let (transmitting, next_poll) = match self.transmit_will_be_finished_at {
            Some(d) if d > *system_time => {
                event!(
                    Level::TRACE,
                    "still transmitting; remaining transmit time is {:?}",
                    d - *system_time
                );
                (true, d)
            }
            None => {
                event!(Level::TRACE, "no transmit has yet been started");
                (false, *system_time + LATER)
            }
            Some(d) => {
                event!(
                    Level::TRACE,
                    "transmission completed {:?} ago, ready to transmit",
                    (*system_time - d)
                );
                (false, *system_time + LATER)
            }
        };
        // next_poll is far in the future if we are already ready to
        // transmit, since we're raising the flag now.  No need to
        // poll us again to discover we're still ready.
        let change_flag = if !self.connected || transmitting {
            None
        } else {
            Some(FlagChange::Raise)
        };
        event!(
            Level::TRACE,
            "connected: {}, flag: {:?}",
            self.connected,
            change_flag
        );
        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag,
            buffer_available_to_cpu: !transmitting,
            inability: false,
            missed_data: false,
            mode: self.mode,
            poll_after: next_poll,
            is_input_unit: false,
        }
    }

    fn connect(&mut self, _system_time: &std::time::Duration, mode: base::Unsigned12Bit) {
        event!(Level::INFO, "{} connected", self.name(),);
        self.connected = true;
        self.mode = mode;
    }

    fn read(&mut self, _system_time: &std::time::Duration) -> Result<MaskedWord, TransferFailed> {
        unreachable!("attempted to read from an output device")
    }

    fn write(
        &mut self,
        system_time: &std::time::Duration,
        source: base::Unsigned36Bit,
    ) -> Result<Option<OutputEvent>, TransferFailed> {
        match self.transmit_will_be_finished_at {
            Some(t) if t > *system_time => {
                event!(
                    Level::DEBUG,
                    "cannot complete TSD, we are already transmitting"
                );
                return Err(TransferFailed::BufferNotFree);
            }
            None => {
                event!(Level::TRACE, "this is the unit's first transmit operation");
            }
            Some(then) => {
                let idle_for = *system_time - then;
                event!(
                    Level::TRACE,
                    "ready to transmit more data (and have been for {idle_for:?}"
                );
            }
        }
        let done_at = *system_time + CHAR_TRANSMIT_TIME;
        event!(
            Level::DEBUG,
            "beginning new transmit operation at {:?}, it will complete at {:?}",
            system_time,
            &done_at
        );
        self.transmit_will_be_finished_at = Some(done_at);
        let char_data = Unsigned6Bit::try_from(u64::from(source) & 0o77)
            .expect("item should only have six value bits (this is a bug)");
        match lincoln_char_to_described_char(char_data, &mut self.state) {
            None => Ok(None),
            Some(described_char) => Ok(Some(OutputEvent::LincolnWriterPrint {
                unit: self.unit,
                ch: described_char,
            })),
        }
    }

    fn name(&self) -> String {
        format!("Lincoln Writer (output), unit {:2o}", self.unit)
    }

    fn transfer_mode(&self) -> crate::TransferMode {
        TransferMode::Exchange
    }

    fn disconnect(&mut self, _system_time: &Duration) {
        self.connected = false;
    }

    fn on_input_event(&mut self, _event: crate::event::InputEvent) {
        // Does nothing
    }
}
