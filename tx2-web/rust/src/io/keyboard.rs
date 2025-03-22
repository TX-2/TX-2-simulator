//! This module implements the keyboard of the Lincoln Writer.
//!
//! A diagram of the keyboard layout appears in the Lincoln Lab
//! Division 6 Quarterly Progress Report, 15 June 1958 (Fig. 63-7, on
//! PDF page 38, page numbered 24).  This diagram is presumably to
//! scale but dimensions are not given on it.  The Lincoln Writer
//! actually has two keyboards.  The keyboard nearest the typist
//! contains decimal digts, majuscule letters (ABC, etc.), the space
//! bar and a few others.  The keyboard further from the typist
//! contains some minuscule latin letters, some Greek letters
//! (minuscule and majuscule) and some symbols (hand, *, arrow, #, ?).
//!
//! The near keyboard produces the symbols shown in the left-hand
//! column of the character set shown in table 7-6 of the TX-2 Lincoln
//! Technical manual, and the far keyboard contains the symbols shown
//! in the right-hand column.
//!
//! Carriage return sets the Lincoln Writer to lower case (and normal
//! script).  See pages 4-37 to 4-42 of the User Handbook.  Since this
//! is presumably for convenience in the common case, and since there
//! is not a full set of minuscule ("abc...") letters on the Lincoln
//! Writer, I infer this to mean that the keyboard farthest from the
//! typist, containing the keys "hijk<>wxyz.." for example, is the in
//! fact the "upper-case" keyboard.  That is, those keys send the
//! "UPPER CASE" (075) code if pressed at (for example) the beginning
//! of a line.
//!
//! Lincoln Writer codes are not unique without knowing the
//! upper/lower case state.  For example, code 26 is sent for both "G"
//! and "w".
//!
//! This interpretation may be wrong.  To make the code in this module
//! slightly less confusing, especially if this interpretation is
//! wrong, we refer to the two keyboards as "Far" and "Near".
//! Assuming a case change is needed, "G" would be sent as 074 026
//! (074 signifying LOWER CASE) and "w" would be sent as 075 026 (075
//! signifying UPPER CASE).  The documentation describes a hardware
//! interlock which keeps a key pressed down while a shift code is
//! sent, so I assume that shift code are only sent when necessary
//! (e.g. "wGG" would be sent as 075 026 075 026 026).
//!
//! The documentation is inconsistent about the codes of some of the
//! keys.  These keys are:
//!
//! CONTINUE: 17 according to the Progress Report ("PR" below) of 15
//! June 1958, but not listed in Table 7-6 of the Technical Manual
//! ("TM" below), which assigns code 17 to YES.
//!
//! YES: 73 according to the PR, 17 according to the TM.
//!
//! NO: 72 according to the PR, 16 according to the TM.
//!
//! LINE FEED UP: not listed in the PR, 73 according to the TM.
//!
//! LINE FEED DOWN: not listed in the PR, 72 according to the TM.
//!
//! The DELETE key in the PR is listed as NULLIFY in the TM.
//!
//! HALT: The label on the top-row hey HALT is hard to read in the PR,
//! but the second digit looks like a 6.  While we might assume code
//! 76 (which is described as STOP in the Technical Manual) that
//! cannot be correct, as there is already a separate key labled STOP.
//! Both are on the top row.  Therefore currently HALT does not
//! generate a character code when pressed.
//!
//! The top-row keys READ IN (14) BEGIN (15), STOP (76), WORD EXAM
//! (71) are coded consistently between the PR and the TM.
//!
//! Using the size of a square key cap as 1x1, dimensions of the other
//! parts of the keyboard are:
//!
//! Total height of keyboard (between top of YES and bottom of space bar): 14.45
//! Total width of keyboard (between LHS of TAB and RHS of NORMAL): 19.7 (but see below).
//!
//! On the RHS of the keyboard unit are three indicator lamps not
//! included in the "width" figure above.  These are circular and have
//! diameter 0.5.  Each is labeled on its LHS.
//!
//! Dimensions (h*w):
//! Regular key: 1*1
//! Gaps between keys: 0.5*0.43
//! Space bar: 1*8.5
//! Wide key (for example RETURN): 1.7*1
//! Tall key (for example HALT): 1.7*1
//! Gap b/w upper and lower keyboards: 1.9
//! Whole unit (incl indicators): 23.8*14.5
//!

use core::fmt::{Debug, Display};
#[cfg(test)]
use std::collections::{HashMap, HashSet};

use conv::*;
use tracing::{event, Level};
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, TextMetrics};

#[cfg(test)]
use base::charset::{
    lincoln_char_to_described_char, Colour, DescribedChar, LincolnState, LwCase, Script,
};
#[cfg(test)]
use base::Unsigned6Bit;

// Horizontal gap between LHS of unit and the first key of each row:
const HPOS_DELETE: f32 = 0.7;
const HPOS_ARROW: f32 = 0.0;
const HPOS_TILDE: f32 = 0.34;
const HPOS_LOGICAL_AND: f32 = 1.0;
const HPOS_TAB: f32 = 0.0;
const HPOS_BLACK: f32 = 0.0;
const HPOS_BACKSPACE: f32 = 0.34;
const HPOS_RETURN: f32 = 0.43;
const HPOS_Z: f32 = 3.6;
const HPOS_SPACE_BAR: f32 = 6.3;

// Vertical gap between top of unit and the first key of each row:
const VPOS_DELETE: f32 = 0.7;
const VPOS_ARROW: f32 = 2.17;
const VPOS_TILDE: f32 = 3.6;
const VPOS_LOGICAL_AND: f32 = 5.0;

const VPOS_TAB: f32 = VPOS_LOGICAL_AND + KEY_HEIGHT + 1.2;
const VPOS_RED: f32 = VPOS_LOGICAL_AND + KEY_HEIGHT + 1.9;
const VPOS_BLACK: f32 = VPOS_RED + KEY_HEIGHT + GAP_HEIGHT;
const VPOS_BACKSPACE: f32 = VPOS_BLACK + KEY_HEIGHT + GAP_HEIGHT;
const VPOS_RETURN: f32 = VPOS_BACKSPACE + KEY_HEIGHT + GAP_HEIGHT;
const VPOS_SPACE_BAR: f32 = VPOS_RETURN + KEY_HEIGHT + GAP_HEIGHT;

// Key dimensions:
const KEY_WIDTH: f32 = 1.0;
const KEY_HEIGHT: f32 = KEY_WIDTH;
const WIDE_KEY_WIDTH: f32 = 1.7;
const TALL_KEY_WIDTH: f32 = KEY_WIDTH;
const GAP_WIDTH: f32 = 0.5;
const GAP_HEIGHT: f32 = 0.43;
const KEY_AND_GAP_WIDTH: f32 = KEY_WIDTH + GAP_WIDTH;
const TALL_KEY_AND_GAP_WIDTH: f32 = TALL_KEY_WIDTH + GAP_WIDTH;
const WIDE_KEY_AND_GAP_WIDTH: f32 = WIDE_KEY_WIDTH + GAP_WIDTH;

const HIT_DETECTION_BACKGROUND: &str = "#ffffff";

/// When the ascent or descent font metrics for a text string are NaN,
/// we fall back on the actual metrics (instead of font metrics).  But
/// the actual metrics don't include the inter-line spacing, so we use
/// a fudge factor to guess at something appropriate.
const FONT_METRIC_FUDGE_FACTOR: f64 = 1.5_f64;

#[derive(Debug)]
enum KeyColour {
    Orange,
    Red,
    Yellow,
    Green,
    Brown,
    Grey,
    Black,
}

impl KeyColour {
    fn key_css_colour(&self) -> &'static str {
        match self {
            KeyColour::Orange => "darkorange",
            KeyColour::Red => "crimson",
            KeyColour::Yellow => "gold",
            KeyColour::Green => "limegreen",
            KeyColour::Brown => "#ba8759", // "Deer"
            KeyColour::Grey => "lightslategrey",
            KeyColour::Black => "black",
        }
    }

    fn label_css_colour(&self) -> &'static str {
        match self {
            KeyColour::Orange
            | KeyColour::Red
            | KeyColour::Yellow
            | KeyColour::Grey
            | KeyColour::Green
            | KeyColour::Brown => "black",
            KeyColour::Black => "white",
        }
    }
}

#[derive(Debug)]
enum KeyShape {
    Square,
    Wide,
    Tall,
    Spacebar,
}

impl KeyShape {
    fn width(&self) -> f32 {
        match self {
            KeyShape::Square | KeyShape::Tall => 1.0,
            KeyShape::Wide => 1.7,
            KeyShape::Spacebar => 8.5,
        }
    }

    fn height(&self) -> f32 {
        match self {
            KeyShape::Square | KeyShape::Wide | KeyShape::Spacebar => 1.0,
            KeyShape::Tall => 1.7,
        }
    }
}

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub(crate) enum Code {
    /// Represents a single key on the Lincoln Writer.  Lincoln Writer
    /// key codes are actually 6 bits but we convert elsewhere.
    Far(u8),
    Near(u8),
    Unknown,
}

impl Debug for Code {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let code = match self {
            Code::Far(code) => {
                f.write_str("Far(")?;
                code
            }
            Code::Near(code) => {
                f.write_str("Near(")?;
                code
            }
            Code::Unknown => {
                return f.write_str("Unknown");
            }
        };
        write!(f, "{code:#o})")
    }
}

pub const SWITCH_TO_FAR: u8 = 0o74; // LOWER CASE
pub const SWITCH_TO_NEAR: u8 = 0o75; // UPPER CASE

impl Code {
    fn hit_detection_rgb(&self) -> [u8; 3] {
        match self {
            Code::Unknown => [0, 0, 0xFF],
            Code::Near(n) => [n * 4, 0, 1],
            Code::Far(n) => [n * 4, 0, 0x80],
        }
    }

    fn hit_detection_colour(&self) -> String {
        let rgb = self.hit_detection_rgb();
        format!("#{:02x}{:02x}{:02x}", rgb[0], rgb[1], rgb[2])
    }

    pub(crate) fn hit_detection_rgb_to_code(r: u8, g: u8, b: u8) -> Result<Option<Code>, String> {
        match (r, g, b) {
            (0xff, 0xff, 0xff) => Ok(None), // not a key at all (i.e. background)
            (0, 0, 0xff) => Ok(Some(Code::Unknown)),
            (n, 0, 0x01) => Ok(Some(Code::Near(n / 4))),
            (n, 0, 0x80) => Ok(Some(Code::Far(n / 4))),
            _ => Err(format!(
                "failed to decode colour (components={:?})",
                (r, g, b)
            )),
        }
    }

    // This function is temporarily test-only because while it has
    // tests, it has no caller yet.
    #[cfg(test)]
    fn hit_detection_colour_to_code(colour: &str) -> Result<Option<Code>, String> {
        let mut components: [u8; 3] = [0, 0, 0];
        for (i, digit) in colour.chars().enumerate() {
            if i == 0 {
                if digit == '#' {
                    continue;
                }
                return Err(format!(
                    "colour should begin with #, but began with {digit}"
                ));
            } else if i > 6 {
                return Err(format!(
                    "colour should have only 6 digits but it has {}",
                    colour.len() - 1
                ));
            }
            if let Ok(n) = hex_digit_value(digit) {
                let pos: usize = (i - 1) / 2;
                components[pos] = components[pos] * 16 + n;
            } else {
                return Err(format!("{digit} is not a valid hex digit"));
            }
        }
        Code::hit_detection_rgb_to_code(components[0], components[1], components[2])
    }
}

#[test]
fn hit_detection_colour_does_not_map_to_a_key_code() {
    let expected: Result<Option<Code>, String> = Ok(None);
    let got = Code::hit_detection_colour_to_code(HIT_DETECTION_BACKGROUND);
    if got == Ok(None) {
        return;
    }
    panic!(
        "Colour {} should map to 'no key' (that is, {:?}) but it actually mapped to {:?}",
        HIT_DETECTION_BACKGROUND, expected, got
    );
}

// This function is temporarily test-only because its sole caller is
// not used yet.
#[cfg(test)]
fn hex_digit_value(ch: char) -> Result<u8, ()> {
    match ch {
        '0' => Ok(0),
        '1' => Ok(1),
        '2' => Ok(2),
        '3' => Ok(3),
        '4' => Ok(4),
        '5' => Ok(5),
        '6' => Ok(6),
        '7' => Ok(7),
        '8' => Ok(8),
        '9' => Ok(9),
        'a' | 'A' => Ok(0xA),
        'b' | 'B' => Ok(0xB),
        'c' | 'C' => Ok(0xC),
        'd' | 'D' => Ok(0xD),
        'e' | 'E' => Ok(0xE),
        'f' | 'F' => Ok(0xF),
        _ => Err(()),
    }
}

#[derive(Debug)]
struct KeyLabel {
    text: &'static [&'static str],
}

#[derive(Debug)]
pub enum KeyPaintError {
    Failed(String),
    TextTooBig {
        msg: String,
        lines: &'static [&'static str],
    },
    InvalidFontMetrics(String),
}

impl Display for KeyPaintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KeyPaintError::Failed(s) | KeyPaintError::InvalidFontMetrics(s) => {
                std::fmt::Display::fmt(&s, f)
            }
            KeyPaintError::TextTooBig { msg, lines } => {
                write!(f, "key label text {lines:?} is too big: {msg}")
            }
        }
    }
}

#[derive(Debug)]
struct Point {
    x: f32,
    y: f32,
}

impl Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({},{})", self.x, self.y)
    }
}

#[derive(Debug)]
struct BoundingBox {
    nw: Point,
    se: Point,
}

impl BoundingBox {
    fn height(&self) -> f32 {
        self.bottom() - self.top()
    }

    fn width(&self) -> f32 {
        self.right() - self.left()
    }

    fn left(&self) -> f32 {
        self.nw.x
    }

    fn right(&self) -> f32 {
        self.se.x
    }

    fn top(&self) -> f32 {
        self.nw.y
    }

    fn bottom(&self) -> f32 {
        self.se.y
    }
}

trait KeyPainter {
    fn width(&self) -> f32;
    fn height(&self) -> f32;
    fn draw_background(&mut self) -> Result<(), KeyPaintError>;
    fn draw_key(
        &mut self,
        keybox: &BoundingBox,
        colour: &KeyColour,
        label: &KeyLabel,
        keycode: Code,
    ) -> Result<(), KeyPaintError>;
}

#[wasm_bindgen]
pub struct HtmlCanvas2DPainter {
    height: f32,
    width: f32,
    context: CanvasRenderingContext2d,
    hits_only: bool,
}

fn keep_greatest<T: PartialOrd, E>(
    accumulator: Option<Result<T, E>>,
    item: Result<T, E>,
) -> Option<Result<T, E>> {
    match (item, accumulator) {
        (Err(e), _) | (_, Some(Err(e))) => Some(Err(e)), // preserve errors
        (Ok(curr), None) => Some(Ok(curr)),
        (Ok(curr), Some(Ok(acc_val))) => {
            if curr > acc_val {
                Some(Ok(curr))
            } else {
                Some(Ok(acc_val))
            }
        }
    }
}

enum Room {
    Sufficient,
    Insufficient(Vec<String>),
}

fn room_for_key_padding(w: f64, h: f64, bbox: &BoundingBox) -> Room {
    const MAX_SIZE_FRACTION: f64 = 0.85;
    let avail_width = f64::from(bbox.width()) * MAX_SIZE_FRACTION;
    let hfit = w <= avail_width;
    let avail_height = f64::from(bbox.height()) * MAX_SIZE_FRACTION;
    let vfit = h <= avail_height;
    if vfit && hfit {
        Room::Sufficient
    } else {
        let mut problems = Vec::with_capacity(2);
        if !hfit {
            problems.push(format!("max text width is {w:.1} but this will not comfortably fit (available width is {avail_width:.1}"));
        }
        if !vfit {
            problems.push(format!("total text height is {h:.1} but this will not comfortably fit (available height is {avail_height:.1}"));
        }
        Room::Insufficient(problems)
    }
}

fn check_font_metric(
    name: &str,
    value: Option<Result<f64, KeyPaintError>>,
) -> Result<f64, KeyPaintError> {
    match value {
        Some(Ok(x)) => {
            if x.is_nan() {
                Err(KeyPaintError::InvalidFontMetrics(format!(
                    "font metric {name} is NaN"
                )))
            } else {
                Ok(x)
            }
        }
        Some(Err(e)) => Err(e),
        None => Ok(0.0),
    }
}

/// Return the distance between the baseline of some measured text and
/// the bottom of whatever would be avove it.  We use font ascent
/// instead of actual ascent, so that we get an appropriate amount of
/// space between lines.  This also gives us some consistency of
/// appearance.  However, if the font ascent metric is not available,
/// we use the actual ascent with a "fudge factor".
fn font_or_actual(
    font_value: f64,
    font_metric_name: &str,
    actual_value: f64,
    actual_metric_name: &str,
) -> Result<f64, KeyPaintError> {
    match (font_value.is_nan(), actual_value.is_nan()) {
        (false, _) => Ok(font_value),
        (true, false) => Ok(actual_value * FONT_METRIC_FUDGE_FACTOR),
        (true, true) => {
            Err(KeyPaintError::InvalidFontMetrics(
                format!("text metric {font_metric_name} is NaN, but fallback metric {actual_metric_name} is also NaN")))
        }
    }
}

fn ascent(metrics: &TextMetrics) -> Result<f64, KeyPaintError> {
    font_or_actual(
        metrics.font_bounding_box_ascent(),
        "font_bounding_box_ascent",
        metrics.actual_bounding_box_ascent(),
        "actual_bounding_box_ascent",
    )
}

fn descent(metrics: &TextMetrics) -> Result<f64, KeyPaintError> {
    font_or_actual(
        metrics.font_bounding_box_descent(),
        "font_bounding_box_descent",
        metrics.actual_bounding_box_descent(),
        "actual_bounding_box_descent",
    )
}

fn bounding_box_width(metrics: &TextMetrics) -> Result<f64, KeyPaintError> {
    match (
        metrics.actual_bounding_box_left(),
        metrics.actual_bounding_box_right(),
    ) {
        (left, _) if left.is_nan() => Err(KeyPaintError::InvalidFontMetrics(
            "actual_bounding_box_left is NaN".to_string(),
        )),
        (_, right) if right.is_nan() => Err(KeyPaintError::InvalidFontMetrics(
            "actual_bounding_box_right is NaN".to_string(),
        )),
        (left, right) => Ok((right - left).abs()),
    }
}

impl HtmlCanvas2DPainter {
    pub fn new(
        context: web_sys::CanvasRenderingContext2d,
        hits_only: bool,
    ) -> Result<HtmlCanvas2DPainter, KeyPaintError> {
        if let Some(canvas) = context.canvas() {
            HtmlCanvas2DPainter::set_up_context_defaults(&context);
            Ok(HtmlCanvas2DPainter {
                height: canvas.height() as f32,
                width: canvas.width() as f32,
                context,
                hits_only,
            })
        } else {
            Err(KeyPaintError::Failed(
                "CanvasRenderingContext2d has no associated canvas".to_string(),
            ))
        }
    }

    fn set_up_context_defaults(context: &CanvasRenderingContext2d) {
        context.set_line_cap("round");
        context.set_stroke_style_str("black");
    }

    fn fill_multiline_text(
        &mut self,
        bbox: &BoundingBox,
        lines: &'static [&'static str],
        colour: &str,
    ) -> Result<(), KeyPaintError> {
        self.context.set_text_baseline("middle");
        let metrics: Vec<TextMetrics> =
            match lines.iter().map(|s| self.context.measure_text(s)).collect() {
                Ok(v) => v,
                Err(e) => {
                    return Err(KeyPaintError::Failed(format!("measure_text failed: {e:?}")));
                }
            };
        let max_ascent = check_font_metric(
            "max ascent",
            metrics.iter().map(ascent).fold(None, keep_greatest),
        )?;
        let max_descent = check_font_metric(
            "max descent",
            metrics.iter().map(descent).fold(None, keep_greatest),
        )?;

        let mw: f64 = match metrics
            .iter()
            .map(bounding_box_width)
            .fold(None, keep_greatest)
        {
            Some(Ok(x)) => x,
            None => 0.0,
            Some(Err(e)) => {
                return Err(e);
            }
        };

        //for (metric, s) in metrics.iter().zip(lines.iter()) {
        //    if metric.actual_bounding_box_left() != 0.0_f64 {
        //        event!(
        //            Level::TRACE,
        //            "left bounding box for {s} is {}",
        //            metric.actual_bounding_box_left()
        //        );
        //    }
        //}
        let (a, d, max_width) = match (max_ascent, max_descent, mw) {
            (a, d, m) if (a == 0.0 && d == 0.0) || m == 0.0 => {
                return Ok(()); // There is no text to draw.
            }
            (a, d, m) => (a, d, m),
        };
        let n = lines.len();
        let line_height: f64 = a + d;
        let total_text_height = line_height * (n as f64);
        if let Room::Insufficient(problems) =
            room_for_key_padding(max_width, total_text_height, bbox)
        {
            return Err(KeyPaintError::TextTooBig {
                msg: format!("no room for key padding: {}", problems.join("\n")),
                lines,
            });
        }
        let x_midline = (bbox.left() + bbox.right()) / 2.0;
        let y_midline = (bbox.top() + bbox.bottom()) / 2.0;
        fn even(n: usize) -> bool {
            n % 2 == 0
        }
        fn yi(i: usize, n: usize, y_midline: f64, a: f64, d: f64) -> f64 {
            let ashift: f64 = if even(n) { a } else { 0.0 };
            fn f(x: usize) -> f64 {
                f64::value_from(x).unwrap_or(f64::MAX)
            }
            let i_minus_floor_half_n = f(i) - f(n / 2).floor();
            y_midline + ashift + i_minus_floor_half_n * (a + d)
        }

        for (i, (s, metrics)) in lines.iter().zip(metrics.iter()).enumerate() {
            let text_y = yi(i, n, y_midline.into(), a, d);

            // This calculation for x assumes Left-to-Right text.
            let text_x: f64 = f64::from(x_midline) - metrics.actual_bounding_box_right() / 2.0;
            self.context.set_fill_style_str(colour);
            if let Err(e) = self.context.fill_text(s, text_x, text_y) {
                return Err(KeyPaintError::Failed(format!("fill_text failed: {e:?}")));
            }
        }
        Ok(())
    }

    fn draw_filled_stroked_rect(&self, x: f64, y: f64, w: f64, h: f64) {
        self.context.fill_rect(x, y, w, h);
        self.context.rect(x, y, w, h);
    }
}

impl KeyPainter for HtmlCanvas2DPainter {
    fn width(&self) -> f32 {
        self.width
    }

    fn height(&self) -> f32 {
        self.height
    }

    fn draw_background(&mut self) -> Result<(), KeyPaintError> {
        if self.hits_only {
            // We fill the background with a colour which never maps back
            // to a key code.
            self.context.set_fill_style_str(HIT_DETECTION_BACKGROUND);
            self.context
                .fill_rect(0.0_f64, 0.0_f64, self.width().into(), self.height().into());
        }
        Ok(())
    }

    fn draw_key(
        &mut self,
        keybox: &BoundingBox,
        colour: &KeyColour,
        label: &KeyLabel,
        keycode: Code,
    ) -> Result<(), KeyPaintError> {
        let hit_detection_colour: String = keycode.hit_detection_colour();

        if self.hits_only {
            self.context
                .set_fill_style_str(hit_detection_colour.as_str());
            self.context.fill_rect(
                keybox.left().into(),
                keybox.top().into(),
                keybox.width().into(),
                keybox.height().into(),
            );
            self.context.stroke();
            return Ok(());
        }

        self.context.set_fill_style_str(colour.key_css_colour());
        self.context.set_stroke_style_str("black");
        let label_css_color = colour.label_css_colour();

        self.draw_filled_stroked_rect(
            keybox.left().into(),
            keybox.top().into(),
            keybox.width().into(),
            keybox.height().into(),
        );
        self.context.stroke();

        let mut current_error: Option<KeyPaintError> = None;
        if !label.text.is_empty() {
            for font_size in (1..=28).rev() {
                let font = format!("{font_size}px sans-serif");
                self.context.set_font(&font);
                match self.fill_multiline_text(keybox, label.text, label_css_color) {
                    Ok(()) => {
                        current_error = None;
                    }
                    Err(KeyPaintError::InvalidFontMetrics(msg)) => {
                        current_error = Some(KeyPaintError::InvalidFontMetrics(format!(
                            "font metrics for {:?} in font '{}' are invalid: {}",
                            label.text, font, msg
                        )));
                    }
                    Err(e) => {
                        current_error = Some(e);
                    }
                }
                match &current_error {
                    Some(KeyPaintError::InvalidFontMetrics(msg)) => {
                        event!(
                            Level::WARN,
                            "Invalid font metrics for '{}' ({}); trying a smaller font size",
                            font,
                            msg
                        );
                        continue; // Try a smaller font size.
                    }
                    Some(KeyPaintError::TextTooBig { msg: _, lines: _ }) => {
                        continue; // Try a smaller font size.
                    }
                    Some(KeyPaintError::Failed(why)) => {
                        return Err(KeyPaintError::Failed(format!(
                            "failed to draw multiline text in font {font_size}: {why}"
                        )));
                    }
                    None => {
                        break;
                    }
                }
            }
        }
        match current_error {
            None => Ok(()),
            Some(error) => Err(error),
        }
    }
}

#[derive(Debug)]
struct Key {
    left: f32,
    top: f32,
    shape: KeyShape,
    colour: KeyColour,
    label: KeyLabel,
    code: Code,
}

fn row0() -> &'static [Key] {
    // This is the top row of the keyboard furthest from the typist.
    const HPOS_YES: f32 = HPOS_DELETE + WIDE_KEY_AND_GAP_WIDTH * 2.0;
    &[
        Key /* DELETE */ {
            left: HPOS_DELETE,
            top: VPOS_DELETE,
            shape: KeyShape::Wide,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["DELETE"],
            },
            code: Code::Far(0o77),
        },
        Key /* STOP */ {
            left: HPOS_DELETE + WIDE_KEY_WIDTH + GAP_WIDTH,
            top: VPOS_DELETE,
            shape: KeyShape::Wide,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &["STOP"],
            },
            code: Code::Far(0o76),
        },
        Key /* YES */ {
            left: HPOS_YES,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["YES"],
            },
            code: Code::Far(0o17),
        },
        Key /* NO */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["NO"],
            },
            // References TM and PR are inconsistent about the coding
            // of this key, we follow the TM, because it is the later
            // document (this page labelled October 1961), but still
            // prior to development of Sketchpad (1963).
            code: Code::Far(0o16),
        },
        Key /* WORD EXAM */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 2.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["WORD", "EXAM"],
            },
            code: Code::Far(0o71),
        },
        Key /* CONTINUE */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 3.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["CON", "TIN", "UE"],
            },
            // The diagram I have seems to show code 0o17 for
            // CONTINUE, but this is not consistent with the LW
            // character set in table 7-6 of the Technical Manual
            // (which says 17 is YES) .  See comment at the top of
            // this file.
            code: Code::Unknown,
        },
        Key /* HALT */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 4.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["HALT"],
            },
            // I can't read the code on the Progress Report diagram
            // for this key.  The second digit may be 6,but the code
            // cannot be 76 as that is the code for STOP which is also
            // shown on the top row in the Progress Report.  So we
            // currently generate not code for HALT.
            code: Code::Unknown,
        },
        Key /* BEGIN */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 5.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["B", "E", "G", "I", "N"],
            },
            code: Code::Far(0o15),
        },
        Key /* READ IN */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["READ", "IN"],
            },
            code: Code::Far(0o14),
        },
        Key /* apostrophe */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0 + KEY_AND_GAP_WIDTH,
            top: VPOS_DELETE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["'"],
            },
            code: Code::Far(0o56),
        },
        Key /* asterisk */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0 + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_DELETE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["*"],
            },
            code: Code::Far(0o57),
        },
        Key /* meta hand */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0 + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_DELETE,
            shape: KeyShape::Wide,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{261E}"],
                // Symbol choices for the "meta hand" were:
                //
                // U+261B, black hand pointing right or
                // U+261E, white hand pointing right
                //
                // The latter is an outlined while the former is a
                // filled symbol.  The outlined symbol is more
                // consistent with the appearance of the key as whown
                // in the illustration in the monthly status report.
                // Unfortunately neither symbol shows a cuff, which
                // does appear in the illustration.
            },
            code: Code::Far(0o00),
        },
    ]
}

fn row1() -> &'static [Key] {
    &[
        Key /* -> */ {
            left: HPOS_ARROW,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2192}"], // rightwards arrow
            },
            code: Code::Far(0o07),
        },
        Key /* ∪ */ {
            left: HPOS_ARROW + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{222A}"], // Union
            },
            code: Code::Far(0o34),
        },
        Key /* ∩ */ {
            left: HPOS_ARROW + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2229}"], // Intersection
            },
            code: Code::Far(0o35),
        },
        Key /* Σ */ {
            left: HPOS_ARROW + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["\u{03A3}"], // Greek capital letter Sigma
            },
            code: Code::Far(0o01),
        },
        Key /* × (multiply) */ {
            left: HPOS_ARROW + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["\u{00D7}"],
            },
            code: Code::Far(0o05),
        },
        Key /* h */ {
            left: HPOS_ARROW + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["h"],
            },
            code: Code::Far(0o44),
        },
        Key /* i */ {
            left: HPOS_ARROW + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["i"],
            },
            code: Code::Far(0o30),
        },
        Key /* j */ {
            left: HPOS_ARROW + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["j"],
            },
            code: Code::Far(0o36),
        },
        Key /* k */ {
            left: HPOS_ARROW + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["k"],
            },
            code: Code::Far(0o37),
        },
        Key /* ε */ {
            left: HPOS_ARROW + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B5}"], // Epsilon (not ∈, Element of)
            },
            code: Code::Far(0o43),
        },
        Key /* λ */ {
            left: HPOS_ARROW + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03BB}"], // Greek small letter lambda, U+03BB
            },
            code: Code::Far(0o50),
        },
        Key /* # */ {
            left: HPOS_ARROW + 11.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["#"],
            },
            code: Code::Far(0o06),
        },
        Key /* ‖ */ {
            left: HPOS_ARROW + 12.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{2016}"], // U+2016, double vertical line
            },
            code: Code::Far(0o03),
        },
        Key /* ? */ {
            left: HPOS_ARROW + 13.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["?"],
            },
            code: Code::Far(0o33),
        },
    ]
}

// missing tests: key codes are unique, key labels consistent with base charset definition

fn row2() -> &'static [Key] {
    &[
        Key /* ~ */ {
            left: HPOS_TILDE,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["~"], // tilde
            },
            code: Code::Far(0o51),
        },
        Key /* ⊃ */ {
            left: HPOS_TILDE + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2283}"], // Superset of
            },
            code: Code::Far(0o45),
        },
        Key /* ⊂ */ {
            left: HPOS_TILDE + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2282}"], // Subset of
            },
            code: Code::Far(0o21),
        },
        Key /* < */ {
            left: HPOS_TILDE + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["<"],
            },
            code: Code::Far(0o10),
        },
        Key /* > */ {
            left: HPOS_TILDE + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &[">"],
            },
            code: Code::Far(0o11),
        },
        Key /* n */ {
            // On the diagram in the progress report (see module
            // header for details) this looks very clearly like a
            // lower-case Greek eta (η, Unicode U+03B7).  However two
            // other considerations make me believe this is in fact n
            // (lower-case N):
            //
            // 1. It's next to "p" on the keyboard
            // 2. The symbol in in the Users Handbook, although hard
            //    to make out, really doesn't look like an eta because
            //    it doesn't have a long tail on the right-hand side.
            left: HPOS_TILDE + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["n"],
            },
            code: Code::Far(0o20),
        },
        Key /* p */ {
            left: HPOS_TILDE + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["p"],
            },
            code: Code::Far(0o42),
        },
        Key /* q */ {
            left: HPOS_TILDE + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["q"],
            },
            code: Code::Far(0o23),
        },
        Key /* t */ {
            left: HPOS_TILDE + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["t"],
            },
            code: Code::Far(0o25),
        },
        Key /* Δ */ {
            left: HPOS_TILDE + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{0394}"], // Greek capital delta, U+0394
            },
            code: Code::Far(0o41),
        },
        Key /* γ */ {
            left: HPOS_TILDE + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B3}"], // Greek small letter gamma (U+03B3)
            },
            code: Code::Far(0o24),
        },
        Key /* { */ {
            left: HPOS_TILDE + 11.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["{"],
            },
            code: Code::Far(0o52),
        },
        Key /* } */ {
            left: HPOS_TILDE + 12.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["}"],
            },
            code: Code::Far(0o53),
        },
        Key /* |, LW code 02 */ {
            left: HPOS_TILDE + 13.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["|"],
            },
            code: Code::Far(0o02),
        },
    ]
}

fn row3() -> &'static [Key] {
    &[
        Key /* ∧ */ {
            left: HPOS_LOGICAL_AND,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2227}"], // U+2227, Logical And
            },
            code: Code::Far(0o47),
        },
        Key /* ∨ */ {
            left: HPOS_LOGICAL_AND + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2228}"], // U+2228, Logical Or
            },
            code: Code::Far(0o22),
        },
        Key /* ≡ */ {
            left: HPOS_LOGICAL_AND + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2261}"], // U+2261, Identical to
            },
            code: Code::Far(0o54),
        },
        Key /* / */ {
            left: HPOS_LOGICAL_AND + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["/"],
            },
            code: Code::Far(0o04),
        },
        Key /* = */ {
            left: HPOS_LOGICAL_AND + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["="],
            },
            code: Code::Far(0o55),
        },
        Key /* w */ {
            left: HPOS_LOGICAL_AND + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["w"],
            },
            code: Code::Far(0o26),
        },
        Key /* x */ {
            left: HPOS_LOGICAL_AND + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["x"],
            },
            code: Code::Far(0o27),
        },
        Key /* y */ {
            left: HPOS_LOGICAL_AND + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["y"],
            },
            code: Code::Far(0o31),
        },
        Key /* z */ {
            left: HPOS_LOGICAL_AND + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["z"],
            },
            code: Code::Far(0o32),
        },
        Key /* α */ {
            left: HPOS_LOGICAL_AND + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B1}"],
            },
            code: Code::Far(0o40),
        },
        Key /* β */ {
            left: HPOS_LOGICAL_AND + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B2}"], // Greek beta symbol, U+03B2
            },
            code: Code::Far(0o46),
        },
        Key {
            // overline
            left: HPOS_LOGICAL_AND + 11.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{0305} "], // Combining overline U+0305
            },
            code: Code::Far(0o12),
        },
        Key {
            // square
            left: HPOS_LOGICAL_AND + 12.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{20DE} "], // combining enclosing square
            },
            code: Code::Far(0o13),
        },
    ]
}

fn row4() -> &'static [Key] {
    // This is the top row of the keyboard nearest the typist.
    &[
        Key /* TAB */ {
            left: HPOS_TAB,
            top: VPOS_TAB,
            shape: KeyShape::Tall,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &["T", "A", "B"],
            },
            code: Code::Near(0o61),
        },
        Key /* RED */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["RED"],
            },
            code: Code::Near(0o67),
        },
        Key /* 0 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["0"],
            },
            code: Code::Near(0o00),
        },
        Key /* 1 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["1"],
            },
            code: Code::Near(0o01),
        },
        Key /* 2 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["2"],
            },
            code: Code::Near(0o02),
        },
        Key /* 3 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["3"],
            },
            code: Code::Near(0o03),
        },
        Key /* 4 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["4"],
            },
            code: Code::Near(0o04),
        },
        Key /* 5 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["5"],
            },
            code: Code::Near(0o05),
        },
        Key /* 6 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["6"],
            },
            code: Code::Near(0o06),
        },
        Key /* 7 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["7"],
            },
            code: Code::Near(0o07),
        },
        Key /* 8 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["8"],
            },
            code: Code::Near(0o10),
        },
        Key /* 9 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["9"],
            },
            code: Code::Near(0o11),
        },
        Key /* underbar */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 12.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{0332} "], // combining low line
            },
            code: Code::Near(0o12),
        },
        Key /* circle */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 13.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &[
                    "\u{20DD} ", // combining enclosing circle
                ]
            },
            code: Code::Near(0o13),
        },
    ]
}

fn row5() -> &'static [Key] {
    const HPOS_Q: f32 = HPOS_BLACK + WIDE_KEY_WIDTH + GAP_WIDTH;
    &[
        Key /* BLACK */ {
            left: HPOS_BLACK,
            top: VPOS_BLACK,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["BLACK"]
            },
            code: Code::Near(0o63),
        },
        Key {
            left: HPOS_Q,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Q"] },
            code: Code::Near(0o40),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 1.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["W"] },
            code: Code::Near(0o46),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["E"] },
            code: Code::Near(0o24),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["R"] },
            code: Code::Near(0o41),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["T"] },
            code: Code::Near(0o43),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Y"] },
            code: Code::Near(0o50),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["U"] },
            code: Code::Near(0o44),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["I"] },
            code: Code::Near(0o30),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["O"] },
            code: Code::Near(0o36),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 9.,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["P"] },
            code: Code::Near(0o37),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["."] },
            code: Code::Near(0o57),
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_BLACK,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel { text: &["SUPER"] },
            code: Code::Near(0o64),
        },
    ]
}

fn row6() -> &'static [Key] {
    const HPOS_A: f32 = HPOS_BACKSPACE + WIDE_KEY_WIDTH + GAP_WIDTH;
    &[
        Key /* BACKSPACE */ {
            left: HPOS_BACKSPACE,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Wide,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &["BACK", "SPACE"]
            },
            code: Code::Near(0o62),
        },
        Key {
            left: HPOS_A,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["A"] },
            code: Code::Near(0o20),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["S"] },
            code: Code::Near(0o42),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["D"] },
            code: Code::Near(0o23),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["F"] },
            code: Code::Near(0o25),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["G"] },
            code: Code::Near(0o26),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["H"] },
            code: Code::Near(0o27),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["J"] },
            code: Code::Near(0o31),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["K"] },
            code: Code::Near(0o32),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["L"] },
            code: Code::Near(0o33),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["+"] },
            code: Code::Near(0o54),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["-"] },
            code: Code::Near(0o55),
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Wide,
            colour: KeyColour::Grey,
            label: KeyLabel { text: &["NORMAL"] },
            code: Code::Near(0o65),
        },
    ]
}

fn row7() -> &'static [Key] {
    &[
        Key /* RETURN */ {
            left: HPOS_RETURN,
            top: VPOS_RETURN,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["RETURN"]
            },
            code: Code::Near(0o60),
        },
        Key {
            left: HPOS_Z,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Z"] },
            code: Code::Near(0o51),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["X"] },
            code: Code::Near(0o47),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["C"] },
            code: Code::Near(0o22),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["V"] },
            code: Code::Near(0o45),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["B"] },
            code: Code::Near(0o21),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["N"] },
            code: Code::Near(0o35),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["M"] },
            code: Code::Near(0o34),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &["("] },
            code: Code::Near(0o52),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &[")"] },
            code: Code::Near(0o53),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &[","] },
            code: Code::Near(0o56),
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_RETURN,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel { text: &["SUB"] },
            code: Code::Near(0o66),
        },
    ]
}

fn row8() -> &'static [Key] {
    &[Key /* space bar */ {
            left: HPOS_SPACE_BAR,
            top: VPOS_SPACE_BAR,
            shape: KeyShape::Spacebar,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &[]
            },
            code: Code::Near(0o70),
        }]
}

fn all_keys() -> impl Iterator<Item = &'static Key> {
    row0()
        .iter()
        .chain(row1().iter())
        .chain(row2().iter())
        .chain(row3().iter())
        .chain(row4().iter())
        .chain(row5().iter())
        .chain(row6().iter())
        .chain(row7().iter())
        .chain(row8().iter())
}

#[test]
fn known_keys_have_unique_codes() {
    let mut codes_seen: HashMap<Code, &'static Key> = HashMap::new();
    for key in all_keys() {
        if key.code == Code::Unknown {
            // This is a key for which the code mapping is not known.
            // Since there is more than one such key, we do not apply
            // the uniqueness constraint to them.
            continue;
        }
        if let Some(previous) = codes_seen.get(&key.code) {
            panic!(
                "duplicate key code {:?} was used for both {:?} and {:?}",
                key.code, key, *previous
            );
        }
        codes_seen.insert(key.code, key);
    }
}

#[cfg(test)]
fn key_code_frequencies() -> HashMap<u8, usize> {
    let mut result: HashMap<u8, usize> = HashMap::new();
    for key in all_keys() {
        match key.code {
            Code::Near(n) | Code::Far(n) => {
                *result.entry(n).or_insert(0) += 1;
            }
            Code::Unknown => (),
        }
    }
    result
}

#[test]
fn codes_used_in_both_near_and_far_keyboards() {
    // Verify that the expected codes appear once, and other codes
    // appear twice (upper and lower case).
    let once_keys: HashSet<u8> = (
        // READ IN, BEGIN, NO, YES
        0o14_u8..=0o17_u8
    )
        .chain(
            // CARRIAGE RETURN, TAB, BACK SPACE, COLOR BLACK, SUPER,
            // NORMAL, SUB, COLOR RED, SPACE, WORD EXAM, LINE FEED DOWN,
            // LINE FEED UP, LOWER CASE, UPPER CASE, STOP, NULLIFY
            0o60..=0o77,
        )
        .collect();
    let key_code_counts = key_code_frequencies();
    for (code, actual_count) in key_code_counts.iter() {
        let expected_count: usize = if once_keys.contains(code) { 1 } else { 2 };
        if *actual_count != expected_count {
            panic!(
                "expected to see code code {:o} with frequency of {} but got frequency of {}",
                code, expected_count, actual_count
            );
        }
    }
}

#[test]
fn all_input_codes_used() {
    let key_code_counts = key_code_frequencies();
    for code in 0..=0o77 {
        match code {
            0o72 | 0o73 => {
                // LINE FEED DOWN and LINE FEED UP don't appear to be
                // generated by keys.  I assume these are used only in
                // Lincoln Writer output, not input.
            }
            0o74 | 0o75 => {
                // LOWER CASE and UPPER CASE are generated by the
                // keyboard, but the keyboard generates them to
                // indicate which keyboard the currently-pressed key
                // belongs to.
            }
            n => {
                if !key_code_counts.contains_key(&n) {
                    panic!("No key generates code {:o}", n);
                }
            }
        }
    }
}

#[test]
fn code_round_trips_as_pixel_colour() {
    for key in all_keys() {
        let colour = key.code.hit_detection_colour();
        match Code::hit_detection_colour_to_code(colour.as_str()) {
            Ok(Some(code)) => {
                assert!(
                    code == key.code,
                    "expected code {:?}, got code {:?}",
                    key.code,
                    code
                );
            }
            Ok(None) => {
                panic!("Key code {:?} round-tripped as if it were the keyboard's background (colour is {})",
                       key.code, colour);
            }
            Err(msg) => {
                panic!("Key code {:?} mapped to hit detection colour {} but this could not be round-tripped: {}", key.code, colour, msg);
            }
        }
    }
}

#[test]
fn known_keys_consistent_with_base_charset() {
    // This test ensures that key code assignments in the keycode
    // implementation are consistent with the code concersion logic in
    // lincoln_char_to_described_char().
    for key in all_keys() {
        let (case, code) = match key.code {
            Code::Near(code) => (LwCase::Lower, code),
            Code::Far(code) => (LwCase::Upper, code),
            Code::Unknown => {
                event!(
                    Level::WARN,
                    "Skipping consistency check for key {key:?} because it has an unknown code",
                );
                continue;
            }
        };
        let mut state = LincolnState {
            script: Script::Normal,
            colour: Colour::Black,
            case,
        };
        let code: Unsigned6Bit = match <Unsigned6Bit as std::convert::TryFrom<u8>>::try_from(code) {
            Ok(x) => x,
            Err(e) => {
                panic!("key code for key {key:?} does not fit into 6 bits: {e}");
            }
        };
        match lincoln_char_to_described_char(code, &mut state) {
            Some(DescribedChar {
                label_matches_unicode: false,
                ..
            }) => {
                // The label on this key isn't supposed to match its
                // Unicode representation.  For example LINE FEED is
                // Unicode '\n'.
            }
            Some(described) => {
                if let Some(unicode) = described.unicode_representation {
                    let unicode_as_string = format!("{unicode}");
                    let one_line_text =
                        key.label.text.iter().fold(String::new(), |mut acc, line| {
                            if !acc.is_empty() {
                                acc.push(' ');
                            }
                            acc.push_str(line);
                            acc
                        });
                    if unicode_as_string != one_line_text {
                        panic!("inconsistency for key {key:?}: label is {:?} (on one line: '{one_line_text}') but lincoln_char_to_described_char calls it '{unicode_as_string}'", key.label.text);
                    }
                }
            }
            None => {
                // Some codes are not expected to have a mapping in
                // lincoln_char_to_described_char.  Some codes we
                // classify here as expect_match=true are handled
                // above by the label_matches_unicode=false case
                // above.  That is, they do have a mapping in
                // lincoln_char_to_described_char but they don't have
                // a unicode representation.
                let expect_match = match u8::from(code) {
                    0o00..=0o13 => true,
                    0o14..=0o17 => false,
                    0o20..=0o57 => true,
                    0o60..=0o77 => false,
                    0o100..=u8::MAX => unreachable!(),
                };
                if expect_match {
                    panic!("key {key:?} has no support in lincoln_char_to_described_char");
                }
            }
        }
    }
}

fn draw_kb<P: KeyPainter>(painter: &mut P) -> Result<(), KeyPaintError> {
    painter.draw_background()?;

    let unit_width = painter.width() / 23.8_f32;
    let unit_height = painter.height() / 14.5_f32;

    for key in all_keys() {
        let left = key.left * unit_width;
        let top = key.top * unit_width;
        let width = key.shape.width() * unit_width;
        let height = key.shape.height() * unit_height;
        let bounds = BoundingBox {
            nw: Point { x: left, y: top },
            se: Point {
                x: left + width,
                y: top + height,
            },
        };
        painter.draw_key(&bounds, &key.colour, &key.label, key.code)?;
    }
    Ok(())
}

#[wasm_bindgen]
pub fn draw_keyboard(painter: &mut HtmlCanvas2DPainter) -> Result<(), JsValue> {
    draw_kb(painter).map_err(|e| e.to_string().into())
}
