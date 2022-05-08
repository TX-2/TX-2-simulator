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
use std::time::Duration;

use atty;
use termcolor::{self, ColorChoice, ColorSpec, StandardStream, WriteColor};
use tracing::{event, Level};

use crate::io::{FlagChange, TransferFailed, Unit, UnitStatus};
use crate::types::*;
use base::charset::{
    self, lincoln_char_to_described_char, DescribedChar, LincolnState,
    LincolnToUnicodeConversionFailure,
};
use base::prelude::*;

//const CHAR_TRANSMIT_TIME: Duration = Duration::from_millis(68);
const LATER: Duration = Duration::from_secs(300);

pub struct LincolnWriterOutput {
    unit: Unsigned6Bit,
    mode: Unsigned12Bit,
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
            transmit_will_be_finished_at: None,
            state: LincolnState::default(),
            colour_choice: get_colour_choice(),
        }
    }

    fn set_colour(&self, col: charset::Colour) {
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

impl Unit for LincolnWriterOutput {
    fn poll(&mut self, system_time: &std::time::Duration) -> UnitStatus {
        let (transmitting, next_poll) = match self.transmit_will_be_finished_at {
            Some(d) if d > *system_time => (true, d),
            _ => (false, *system_time + LATER),
        };
        UnitStatus {
            special: Unsigned12Bit::ZERO,
            change_flag: if transmitting {
                None
            } else {
                Some(FlagChange::Raise)
            },
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
                return Err(TransferFailed::BufferNotFree);
            }
            None | Some(_) => (),
        }
        let char_data = u8::try_from(u64::from(source) & 0o77)
            .expect("item should only have six value bits (this is a bug)");
        let prev_colour = self.state.colour;
        match lincoln_char_to_described_char(&char_data, &mut self.state) {
            Ok(Some(DescribedChar {
                display: Some('\r'),
                ..
            })) => {
                println!();
                Ok(())
            }
            Ok(Some(DescribedChar {
                display: Some(ch), ..
            })) => {
                print!("{}", ch);
                Ok(())
            }
            Ok(Some(DescribedChar {
                display: None,
                base_char,
                ..
            })) => {
                // We just emit it in normal script.
                print!("{}", base_char);
                Ok(())
            }
            Ok(None) => {
                if self.state.colour != prev_colour {
                    self.set_colour(self.state.colour);
                }
                Ok(())
            }
            Err(LincolnToUnicodeConversionFailure::CannotSuperscript(_, base)) => {
                // This is a character which is superscript in the
                // Lincoln Writer representation but for which we have
                // not been able to find a suitable Unicode
                // representation.
                print!("{}", base);
                Ok(())
            }
            Err(LincolnToUnicodeConversionFailure::CannotSubscript(_, base)) => {
                // This is a character which is subscript in the
                // Lincoln Writer representation but for which we have
                // not been able to find a suitable Unicode
                // representation.
                print!("{}", base);
                Ok(())
            }
            Err(LincolnToUnicodeConversionFailure::CharacterOutOfRange(_)) => unreachable!(),
            Err(LincolnToUnicodeConversionFailure::NoMapping(_)) => {
                // Some Lincoln Writer characters generate codes on
                // input, but the Lincoln Writer does nothing with
                // them.  These characters generate a NoMapping error.
                // The real Lincoln Writer tooka non-zero time to
                // process these characters but otherwise did nothing.
                // We do nothing also, but probably faster.
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
