use base::charset::DescribedChar;
use base::Unsigned6Bit;

#[derive(Debug)]
pub enum InputEvent {
    PetrMountPaperTape { data: Vec<u8> },
    LwKeyboardInput { data: Vec<Unsigned6Bit> },
}

#[derive(Debug)]
pub enum InputEventResult {
    Ok,   // input accepted
    Busy, // not accepted
    InputEventNotValidForDevice,
    InvalidReentrantCall,
    UnknownSource, // source not recognised
}

#[derive(Debug, PartialEq, Eq)]
pub enum OutputEvent {
    LincolnWriterPrint {
        unit: Unsigned6Bit,
        ch: DescribedChar,
    },
}
