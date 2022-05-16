use base::charset::DescribedChar;
use base::Unsigned6Bit;

#[derive(Debug)]
pub enum InputEvent {
    PetrMountPaperTape { data: Vec<u8> },
}

#[derive(Debug, PartialEq, Eq)]
pub enum OutputEvent {
    LincolnWriterPrint {
        unit: Unsigned6Bit,
        ch: DescribedChar,
    },
}
