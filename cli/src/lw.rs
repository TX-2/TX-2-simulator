use std::io::{stdout, Write};

use termcolor::{self, ColorChoice, ColorSpec, StandardStream, WriteColor};
use tracing::{event, Level};

use base::charset::{self, DescribedChar, LincolnChar, LincolnState};

pub struct LincolnStreamWriter {
    current_attributes: LincolnState,
    stream: StandardStream,
}

fn get_colour_choice() -> termcolor::ColorChoice {
    if atty::is(atty::Stream::Stdout) {
        ColorChoice::Auto
    } else {
        ColorChoice::Never
    }
}

impl LincolnStreamWriter {
    pub fn new() -> LincolnStreamWriter {
        LincolnStreamWriter {
            current_attributes: LincolnState::default(),
            stream: StandardStream::stdout(get_colour_choice()),
        }
    }

    fn set_lw_colour(&mut self, col: charset::Colour) {
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
        if let Err(e) = self.stream.set_color(&new_colour) {
            event!(
                Level::ERROR,
                "Failed to select colour {:?}: {}",
                new_colour,
                e
            );
        }
    }

    pub fn write(&mut self, item: DescribedChar) -> Result<(), std::io::Error> {
        let prev_colour = self.current_attributes.colour;
        if item.attributes.colour != prev_colour {
            self.set_lw_colour(item.attributes.colour);
        }
        let to_emit: char = match item {
            DescribedChar {
                unicode_representation: None,
                base_char: LincolnChar::Unprintable(_),
                ..
            } => {
                return Ok(());
            }
            DescribedChar {
                unicode_representation: Some('\r'),
                ..
            } => '\n',
            DescribedChar {
                unicode_representation: Some(ch),
                ..
            } => ch,
            DescribedChar {
                unicode_representation: None,
                base_char: LincolnChar::UnicodeBaseChar(base),
                ..
            } => {
                // We just emit it in normal script.
                base
            }
        };
        let stdout = stdout();
        let mut handle = stdout.lock();
        write!(handle, "{to_emit}").and_then(|()| handle.flush())
    }

    pub fn disconnect(&mut self) {
        if let Err(e) = self.stream.reset() {
            event!(Level::ERROR, "Failed to reset terminal: {}", e);
        }
    }
}
