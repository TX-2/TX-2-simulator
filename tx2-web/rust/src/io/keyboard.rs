//! This module implements the keyboard of the Lincoln Writer.
//!
//! A diagram of the keyboard layout appears in the Lincoln Lab
//! Division 6 Quarterly Progress Report, 15 June 1958.  This disgram
//! is presumably to scale but dimensions are not given on it.
//!
//! Using the size of a square key cap as 1x1, dimentions of the other
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

use core::fmt::Display;

use conv::*;
use tracing::{event, Level};
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, TextMetrics};

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

#[derive(Debug)]
struct KeyLabel {
    text: &'static [&'static str],
}

#[derive(Debug)]
pub enum KeyPaintError {
    Failed(String),
    TextTooBig,
}

impl Display for KeyPaintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KeyPaintError::Failed(s) => s.fmt(f),
            KeyPaintError::TextTooBig => f.write_str("key label text is too big"),
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
    fn draw_key(
        &mut self,
        keybox: &BoundingBox,
        colour: &KeyColour,
        label: &KeyLabel,
    ) -> Result<(), KeyPaintError>;
}

#[wasm_bindgen]
pub struct HtmlCanvas2DPainter {
    height: f32,
    width: f32,
    context: CanvasRenderingContext2d,
}

fn keep_greatest<T: PartialOrd>(acc: Option<T>, item: T) -> Option<T> {
    if let Some(max) = acc {
        if item > max {
            Some(item)
        } else {
            Some(max)
        }
    } else {
        Some(item)
    }
}

fn room_for_key_padding(w: f64, h: f64, bbox: &BoundingBox) -> bool {
    const MAX_SIZE_FRACTION: f64 = 0.85;
    let avail_width = f64::from(bbox.width()) * MAX_SIZE_FRACTION;
    let hfit = w <= avail_width;
    let avail_height = f64::from(bbox.height()) * MAX_SIZE_FRACTION;
    let vfit = h <= avail_height;
    if !hfit {
        event!(Level::INFO, "max text width is {w:.1} but this will not comfortably fit (available width is {avail_width:.1}");
    }
    if !vfit {
        event!(Level::INFO, "total text height is {h:.1} but this will not comfortably fit (available height is {avail_height:.1}");
    }
    hfit && vfit
}

impl HtmlCanvas2DPainter {
    pub fn new(
        context: web_sys::CanvasRenderingContext2d,
    ) -> Result<HtmlCanvas2DPainter, KeyPaintError> {
        if let Some(canvas) = context.canvas() {
            HtmlCanvas2DPainter::set_up_context_defaults(&context);
            Ok(HtmlCanvas2DPainter {
                height: canvas.height() as f32,
                width: canvas.width() as f32,
                context,
            })
        } else {
            Err(KeyPaintError::Failed(
                "CanvasRenderingContext2d has no associated canvas".to_string(),
            ))
        }
    }

    fn set_up_context_defaults(context: &CanvasRenderingContext2d) {
        context.set_line_cap("round");
        context.set_stroke_style(&("black".into()));
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

        // We use font ascent/descent instead of actual
        // ascent/descent, so that we get space between lines.  This
        // also gives us some consistency of appearance.
        let max_ascent = metrics
            .iter()
            .map(|m| m.font_bounding_box_ascent())
            .fold(None, keep_greatest);
        let max_descent = metrics
            .iter()
            .map(|m| m.font_bounding_box_descent())
            .fold(None, keep_greatest);
        let mw: Option<f64> = metrics
            .iter()
            .map(|m| (m.actual_bounding_box_right() - m.actual_bounding_box_left()).abs())
            .fold(None, keep_greatest);
        for (metric, s) in metrics.iter().zip(lines.iter()) {
            if metric.actual_bounding_box_left() != 0.0_f64 {
                event!(
                    Level::DEBUG,
                    "left bounding box for {s} is {}",
                    metric.actual_bounding_box_left()
                );
            }
        }
        let (a, d, max_width) = match (max_ascent, max_descent, mw) {
            (Some(a), Some(d), Some(m)) => (a, d, m),
            _ => {
                return Ok(()); // There is no text to draw.
            }
        };
        let n = lines.len();
        let line_height: f64 = a + d;
        let total_text_height = line_height * (n as f64);
        event!(
            Level::DEBUG,
            "line height is {line_height:.1}; total text height is {total_text_height:.1}"
        );
        if !room_for_key_padding(max_width, total_text_height, bbox) {
            return Err(KeyPaintError::TextTooBig);
        }
        let x_midline = (bbox.left() + bbox.right()) / 2.0;
        let y_midline = (bbox.top() + bbox.bottom()) / 2.0;
        event!(Level::DEBUG, "y_midline is {y_midline:.1}");
        fn even(n: usize) -> bool {
            n % 2 == 0
        }
        fn yi(i: usize, n: usize, y_midline: f64, a: f64, d: f64) -> f64 {
            let ashift: f64 = if even(n) { a } else { 0.0 };
            fn f(x: usize) -> f64 {
                f64::value_from(x).unwrap_or(f64::MAX)
            }
            let i_minus_floor_half_n = f(i) - f(n / 2).floor();
            let result = y_midline + ashift + i_minus_floor_half_n * (a + d);
            event!(
                Level::DEBUG,
                "yi: i={i}, n={n}, ashift={ashift:.0} y_midline={y_midline:.0}, result={result}"
            );
            result
        }

        for (i, (s, metrics)) in lines.iter().zip(metrics.iter()).enumerate() {
            let text_y = yi(i, n, y_midline.into(), a, d);
            event!(
                Level::DEBUG,
                "fill_multiline_text: drawing {s:?} at y={text_y:.1}"
            );
            // This calculation for x assumes Left-to-Right text.
            let text_x: f64 = f64::from(x_midline) - metrics.actual_bounding_box_right() / 2.0;
            self.context.set_fill_style(&JsValue::from(colour));
            if let Err(e) = self.context.fill_text(s, text_x, text_y) {
                return Err(KeyPaintError::Failed(format!("fill_text failed: {e:?}")));
            }
            //self.context.set_stroke_style(&("blue".into()));
            //let eps: f64 = 6.0;
            //self.context.move_to(f64::from(bbox.left()) - eps, text_y);
            //self.context.line_to(f64::from(bbox.right()) + eps, text_y);
            //self.context.stroke();
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

    fn draw_key(
        &mut self,
        keybox: &BoundingBox,
        colour: &KeyColour,
        label: &KeyLabel,
    ) -> Result<(), KeyPaintError> {
        event!(
            Level::DEBUG,
            "draw_key {label:?} at {} ->  {}",
            keybox.nw,
            keybox.se
        );
        self.context.set_fill_style(&colour.key_css_colour().into());
        self.context.set_stroke_style(&("black".into()));
        self.draw_filled_stroked_rect(
            keybox.left().into(),
            keybox.top().into(),
            keybox.width().into(),
            keybox.height().into(),
        );
        self.context.stroke();

        let mut successfully_drew_text = false;
        for font_size in (1..=28).rev() {
            let font = format!("{font_size}px sans-serif");
            self.context.set_font(&font);
            event!(Level::DEBUG, "Trying font '{font}' for label {label:?}");
            match self.fill_multiline_text(keybox, label.text, colour.label_css_colour()) {
                Err(KeyPaintError::TextTooBig) => {
                    continue; // Try a smaller font size.
                }
                Err(KeyPaintError::Failed(why)) => {
                    return Err(KeyPaintError::Failed(format!(
                        "failed to draw multiline text in font {font_size}: {why}"
                    )));
                }
                Ok(()) => {
                    successfully_drew_text = true;
                    event!(Level::DEBUG, "Chose font '{font}' for label {label:?}");
                    break;
                }
            }
        }
        if successfully_drew_text {
            Ok(())
        } else {
            Err(KeyPaintError::TextTooBig)
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
}

fn row0() -> &'static [Key] {
    const HPOS_YES: f32 = HPOS_DELETE + WIDE_KEY_AND_GAP_WIDTH * 2.0;
    &[
        Key /* DELETE */ {
            left: HPOS_DELETE,
            top: VPOS_DELETE,
            shape: KeyShape::Wide,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["DELETE"],
            }
        },
        Key /* STOP */ {
            left: HPOS_DELETE + WIDE_KEY_WIDTH + GAP_WIDTH,
            top: VPOS_DELETE,
            shape: KeyShape::Wide,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &["STOP"],
            }
        },
        Key /* YES */ {
            left: HPOS_YES,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["YES"],
            }
        },
        Key /* NO */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["NO"],
            }
        },
        Key /* WORD EXAM */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 2.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["WORD", "EXAM"],
            }
        },
        Key /* CONTINUE */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 3.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["CON", "TIN", "UE"],
            }
        },
        Key /* HALT */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 4.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["HALT"],
            }
        },
        Key /* BEGIN */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 5.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["B", "E", "G", "I", "N"],
            }
        },
        Key /* READ IN */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0,
            top: 0.0,
            shape: KeyShape::Tall,
            colour: KeyColour::Black,
            label: KeyLabel {
                text: &["READ", "IN"],
            }
        },
        Key /* apostrophe */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0 + KEY_AND_GAP_WIDTH,
            top: VPOS_DELETE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["'"],
            }
        },
        Key /* asterisk */ {
            left: HPOS_YES + TALL_KEY_AND_GAP_WIDTH * 6.0 + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_DELETE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["*"],
            }
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
            }
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
            }
        },
        Key /* ∪ */ {
            left: HPOS_ARROW + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{222A}"], // Union
            }
        },
        Key /* ∩ */ {
            left: HPOS_ARROW + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2229}"], // Intersection
            }
        },
        Key /* Σ */ {
            left: HPOS_ARROW + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["\u{03A3}"], // Greek capital letter Sigma
            }
        },
        Key /* × (multiply) */ {
            left: HPOS_ARROW + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["\u{00D7}"],
            }
        },
        Key /* h */ {
            left: HPOS_ARROW + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["h"],
            },
        },
        Key /* i */ {
            left: HPOS_ARROW + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["i"],
            },
        },
        Key /* j */ {
            left: HPOS_ARROW + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["j"],
            },
        },
        Key /* k */ {
            left: HPOS_ARROW + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["k"],
            },
        },
        Key /* ∈ */ {
            left: HPOS_ARROW + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{2208}"], // ∈, Element of
            }
        },
        Key /* λ */ {
            left: HPOS_ARROW + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03BB}"], // Greek small letter lambda, U+03BB
            }
        },
        Key /* # */ {
            left: HPOS_ARROW + 11.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["#"],
            },
        },
        Key /* ‖ */ {
            left: HPOS_ARROW + 12.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{2016}"], // U+2016, double vertical line
            },
        },
        Key /* ? */ {
            left: HPOS_ARROW + 13.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_ARROW,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["?"],
            },
        },
    ]
}

fn row2() -> &'static [Key] {
    &[
        Key /* ~ */ {
            left: HPOS_TILDE,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["~"], // tilde
            }
        },
        Key /* ⊃ */ {
            left: HPOS_TILDE + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2283}"], // Superset of
            }
        },
        Key /* ⊂ */ {
            left: HPOS_TILDE + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2282}"], // Subset of
            }
        },
        Key /* < */ {
            left: HPOS_TILDE + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["<"],
            }
        },
        Key /* > */ {
            left: HPOS_TILDE + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &[">"],
            }
        },
        Key /* Δ */ {
            left: HPOS_TILDE + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{0394}"], // Greek capital delta, U+0394
            }
        },
        Key /* γ */ {
            left: HPOS_TILDE + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B3}"], // Greek small letter gamma (U+03B3)
            }
        },
        Key /* { */ {
            left: HPOS_TILDE + 11.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["{"],
            }
        },
        Key /* } */ {
            left: HPOS_TILDE + 12.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["}"],
            }
        },
        Key /* |, LW code 02 */ {
            left: HPOS_TILDE + 13.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["|"],
            }
        },
        Key /* n */ {
            left: HPOS_TILDE + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["n"],
            },
        },
        Key /* p */ {
            left: HPOS_TILDE + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["p"],
            },
        },
        Key /* q */ {
            left: HPOS_TILDE + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["q"],
            },
        },
        Key /* t */ {
            left: HPOS_TILDE + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_TILDE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["t"],
            },
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
            }
        },
        Key /* ∨ */ {
            left: HPOS_LOGICAL_AND + 1.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2228}"], // U+2228, Logical Or
            }
        },
        Key /* ≡ */ {
            left: HPOS_LOGICAL_AND + 2.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Brown,
            label: KeyLabel {
                text: &["\u{2261}"], // U+2261, Identical to
            }
        },
        Key /* / */ {
            left: HPOS_LOGICAL_AND + 3.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["/"],
            }
        },
        Key /* = */ {
            left: HPOS_LOGICAL_AND + 4.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["="],
            }
        },
        Key /* w */ {
            left: HPOS_LOGICAL_AND + 5.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["w"],
            },
        },
        Key /* x */ {
            left: HPOS_LOGICAL_AND + 6.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["x"],
            },
        },
        Key /* y */ {
            left: HPOS_LOGICAL_AND + 7.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["y"],
            },
        },
        Key /* z */ {
            left: HPOS_LOGICAL_AND + 8.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel {
                text: &["z"],
            },
        },
        Key /* α */ {
            left: HPOS_LOGICAL_AND + 9.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B1}"],
            },
        },
        Key /* β */ {
            left: HPOS_LOGICAL_AND + 10.0 * KEY_AND_GAP_WIDTH,
            top: VPOS_LOGICAL_AND,
            shape: KeyShape::Square,
            colour: KeyColour::Orange,
            label: KeyLabel {
                text: &["\u{03B2}"], // Greek beta symbol, U+03B2
            },
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
        },
    ]
}

fn row4() -> &'static [Key] {
    &[
        Key /* TAB */ {
            left: HPOS_TAB,
            top: VPOS_TAB,
            shape: KeyShape::Tall,
            colour: KeyColour::Grey,
            label: KeyLabel {
                text: &["T", "A", "B"],
            }
        },
        Key /* RED */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["RED"],
            }
        },
        Key /* 0 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["0"],
            }
        },
        Key /* 1 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["1"],
            }
        },
        Key /* 2 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["2"],
            }
        },
        Key /* 3 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["3"],
            }
        },
        Key /* 4 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["4"],
            }
        },
        Key /* 5 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["5"],
            }
        },
        Key /* 6 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["6"],
            }
        },
        Key /* 7 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["7"],
            }
        },
        Key /* 8 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["8"],
            }
        },
        Key /* 9 */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel {
                text: &["9"],
            }
        },
        Key /* underbar */ {
            left: HPOS_TAB + KEY_AND_GAP_WIDTH * 12.0,
            top: VPOS_RED,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel {
                text: &["\u{0332} "], // combining low line
            }
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
            }
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
            }
        },
        Key {
            left: HPOS_Q,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Q"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 1.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["W"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["E"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["R"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["T"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Y"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["U"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["I"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["O"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 9.,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["P"] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_BLACK,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["."] },
        },
        Key {
            left: HPOS_Q + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_BLACK,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel { text: &["SUPER"] },
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
            }
        },
        Key {
            left: HPOS_A,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["A"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["S"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["D"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["F"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["G"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["H"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["J"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["K"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["L"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["+"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Square,
            colour: KeyColour::Yellow,
            label: KeyLabel { text: &["-"] },
        },
        Key {
            left: HPOS_A + KEY_AND_GAP_WIDTH * 11.0,
            top: VPOS_BACKSPACE,
            shape: KeyShape::Wide,
            colour: KeyColour::Grey,
            label: KeyLabel { text: &["NORMAL"] },
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
            }
        },
        Key {
            left: HPOS_Z,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["Z"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["X"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 2.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["C"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 3.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["V"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 4.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["B"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 5.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["N"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 6.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Green,
            label: KeyLabel { text: &["M"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 7.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &["("] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 8.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &[")"] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 9.0,
            top: VPOS_RETURN,
            shape: KeyShape::Square,
            colour: KeyColour::Red,
            label: KeyLabel { text: &[","] },
        },
        Key {
            left: HPOS_Z + KEY_AND_GAP_WIDTH * 10.0,
            top: VPOS_RETURN,
            shape: KeyShape::Wide,
            colour: KeyColour::Black,
            label: KeyLabel { text: &["SUB"] },
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
            }
        }]
}

fn draw_kb<P: KeyPainter>(painter: &mut P) -> Result<(), KeyPaintError> {
    let unit_width = painter.width() / 23.8_f32;
    let unit_height = painter.height() / 14.5_f32;

    for key in row0()
        .iter()
        .chain(row1().iter())
        .chain(row2().iter())
        .chain(row3().iter())
        .chain(row4().iter())
        .chain(row5().iter())
        .chain(row6().iter())
        .chain(row7().iter())
        .chain(row8().iter())
    {
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
        painter.draw_key(&bounds, &key.colour, &key.label)?;
    }
    Ok(())
}

#[wasm_bindgen]
pub fn draw_keyboard(painter: &mut HtmlCanvas2DPainter) -> Result<(), JsValue> {
    draw_kb(painter).map_err(|e| e.to_string().into())
}
