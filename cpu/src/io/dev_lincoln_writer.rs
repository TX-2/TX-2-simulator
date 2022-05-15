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
use std::io::{stdout, Write};
use std::time::Duration;

use crate::io::{FlagChange, TransferFailed, Unit, UnitStatus};
use crate::types::*;
use atty;
use base::charset::{
    self, lincoln_char_to_described_char, DescribedChar, LincolnState,
    LincolnToUnicodeConversionFailure,
};
use base::prelude::*;
use termcolor::{self, ColorChoice, ColorSpec, StandardStream, WriteColor};
use tracing::{event, Level};

const CHAR_TRANSMIT_TIME: Duration = Duration::from_millis(68);
const LATER: Duration = Duration::from_secs(300);

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
    colour_choice: termcolor::ColorChoice,
}

fn get_colour_choice() -> termcolor::ColorChoice {
    if atty::is(atty::Stream::Stdout) {
        ColorChoice::Auto
    } else {
        ColorChoice::Never
    }
}

impl LincolnWriterOutput {
    pub fn new(unit: Unsigned6Bit) -> LincolnWriterOutput {
        LincolnWriterOutput {
            unit,
            mode: Unsigned12Bit::ZERO,
            connected: false,
            transmit_will_be_finished_at: None,
            state: LincolnState::default(),
            colour_choice: get_colour_choice(),
        }
    }

    fn set_lw_colour(&self, col: charset::Colour) {
        let mut stdout = StandardStream::stdout(self.colour_choice);
        let mut new_colour = ColorSpec::new();
        match col {
            charset::Colour::Black => {
                new_colour
                    .set_fg(Some(termcolor::Color::White))
                    .set_bg(Some(termcolor::Color::Black));
            }
            charset::Colour::Red => {
                new_colour
                    .set_fg(Some(termcolor::Color::Black))
                    .set_bg(Some(termcolor::Color::Black));
            }
        }
        if let Err(e) = stdout.set_color(&new_colour) {
            event!(
                Level::ERROR,
                "Failed to select colour {:?}: {}",
                new_colour,
                e
            );
        }
    }
}

enum EmitItem {
    Newline,
    ColourChange(charset::Colour),
    Char(char),
}

fn char_to_write(char_data: u8, state: &mut LincolnState) -> Option<EmitItem> {
    let prev_colour = state.colour;
    match lincoln_char_to_described_char(&char_data, state) {
        Ok(Some(DescribedChar {
            display: Some('\r'),
            ..
        })) => Some(EmitItem::Newline),
        Ok(Some(DescribedChar {
            display: Some(ch), ..
        })) => Some(EmitItem::Char(ch)),
        Ok(Some(DescribedChar {
            display: None,
            base_char,
            ..
        })) => {
            // We just emit it in normal script.
            Some(EmitItem::Char(base_char))
        }
        Ok(None) => {
            if state.colour != prev_colour {
                Some(EmitItem::ColourChange(state.colour))
            } else {
                None
            }
        }
        Err(LincolnToUnicodeConversionFailure::CannotSuperscript(_, base)) => {
            // This is a character which is superscript in the
            // Lincoln Writer representation but for which we have
            // not been able to find a suitable Unicode
            // representation.
            Some(EmitItem::Char(base))
        }
        Err(LincolnToUnicodeConversionFailure::CannotSubscript(_, base)) => {
            // This is a character which is subscript in the
            // Lincoln Writer representation but for which we have
            // not been able to find a suitable Unicode
            // representation.
            Some(EmitItem::Char(base))
        }
        Err(LincolnToUnicodeConversionFailure::CharacterOutOfRange(_)) => unreachable!(),
        Err(LincolnToUnicodeConversionFailure::NoMapping(_)) => {
            // Some Lincoln Writer characters generate codes on
            // input, but the Lincoln Writer does nothing with
            // them.  These characters generate a NoMapping error.
            // The real Lincoln Writer tooka non-zero time to
            // process these characters but otherwise did nothing.
            // We do nothing also, but probably faster.
            None
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
    ) -> Result<(), TransferFailed> {
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
        let char_data = u8::try_from(u64::from(source) & 0o77)
            .expect("item should only have six value bits (this is a bug)");
        match char_to_write(char_data, &mut self.state) {
            None => Ok(()),
            Some(thing) => {
                if let Err(e) = {
                    let out: Option<char> = match thing {
                        EmitItem::ColourChange(newcol) => {
                            self.set_lw_colour(newcol);
                            None
                        }
                        EmitItem::Newline => Some('\n'),
                        EmitItem::Char(ch) => Some(ch),
                    };
                    if let Some(ch) = out {
                        let stdout = stdout();
                        let mut handle = stdout.lock();
                        write!(handle, "{}", ch).and_then(|()| handle.flush())
                    } else {
                        Ok(())
                    }
                } {
                    event!(Level::WARN, "Write error on stdout: {}", e);
                }
                Ok(())
            }
        }
    }

    fn name(&self) -> String {
        format!("Lincoln Writer (output), unit {:2o}", self.unit)
    }

    fn transfer_mode(&self) -> crate::TransferMode {
        TransferMode::Exchange
    }
}
