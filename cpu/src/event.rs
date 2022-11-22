use std::error::Error;
use std::fmt::{self, Display, Formatter};

use base::charset::DescribedChar;
use base::Unsigned6Bit;

#[derive(Debug)]
pub enum InputEvent {
    PetrMountPaperTape { data: Vec<u8> },
    LwKeyboardInput { data: Vec<Unsigned6Bit> },
}

#[derive(Debug)]
pub enum InputEventError {
    /// BufferUnavailable simply means that an input event has
    /// occurred on a device whose buffer is still being used by the
    /// CPU.  Sometimes this can happen if the program running on the
    /// TX-2 makes use of the hold bit too much in some sequence, with
    /// the result that the sequence that should be reading the device
    /// (and hence freeing the buffer) isn't getting a chance to do
    /// this.
    BufferUnavailable,

    /// InputOnUnattachedUnit means that the user has generated input
    /// on a unit which has not been attached.  That is, the simulator
    /// does not believe that this hardware exists in the system at
    /// all.  This would likely be due to some configuration
    /// inconsistency between the user interface and the simulator
    /// core.
    InputOnUnattachedUnit,

    InputEventNotValidForDevice,
    InvalidReentrantCall,
}

impl Display for InputEventError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(match self {
            InputEventError::BufferUnavailable => "buffer unavailable",
            InputEventError::InputOnUnattachedUnit => "input on a unit which is not attached",
            InputEventError::InputEventNotValidForDevice => {
                "input event is not valid for this device"
            }
            InputEventError::InvalidReentrantCall => "inalid re-entrant call",
        })
    }
}

impl Error for InputEventError {}

#[derive(Debug, PartialEq, Eq)]
pub enum OutputEvent {
    LincolnWriterPrint {
        unit: Unsigned6Bit,
        ch: DescribedChar,
    },
}
