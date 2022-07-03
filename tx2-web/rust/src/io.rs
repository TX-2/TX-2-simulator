use core::fmt::Display;

use std::collections::BTreeMap;

use conv::*;
use js_sys::Array;
use serde::Serialize;
use wasm_bindgen::prelude::*;
use web_sys::{CanvasRenderingContext2d, TextMetrics};

use cpu::*;

use crate::context::make_context;
use crate::samples::sample_binary_hello;

#[wasm_bindgen]
pub fn tx2_load_tape(tx2: &mut Tx2, simulated_time: f64, elapsed_time_secs: f64, data: &[u8]) {
    let context = make_context(simulated_time, elapsed_time_secs);
    tx2.mount_tape(&context, data.to_vec());
}

#[wasm_bindgen]
pub fn get_builtin_sample_tape(sample_name: &str) -> Result<Vec<u8>, String> {
    match sample_name {
        "hello" => Ok(sample_binary_hello()),
        _ => Err(format!("unknown sample file '{}'", sample_name)),
    }
    .map(|data| data.to_vec())
}

#[derive(Debug, Serialize)]
pub struct UnitState {
    unit: u8,
    unit_state: ExtendedUnitState,
}

#[wasm_bindgen]
pub fn tx2_drain_device_changes(
    tx2: &mut Tx2,
    simulated_system_time_secs: f64,
    elapsed_time_secs: f64,
) -> Result<JsValue, String> {
    let context = make_context(simulated_system_time_secs, elapsed_time_secs);
    match tx2.drain_device_changes(&context) {
        Ok(changes) => {
            let change_map: BTreeMap<u8, UnitState> = changes
                .into_iter()
                .map(|(unit, state)| {
                    (
                        u8::from(unit),
                        UnitState {
                            unit: unit.into(),
                            unit_state: state,
                        },
                    )
                })
                .collect();
            serde_wasm_bindgen::to_value(&change_map).map_err(|e| e.to_string())
        }
        Err(e) => Err(e.to_string()),
    }
}

#[wasm_bindgen]
pub fn tx2_device_statuses(
    tx2: &mut Tx2,
    simulated_system_time_secs: f64,
    elapsed_time_secs: f64,
) -> Array {
    let context = make_context(simulated_system_time_secs, elapsed_time_secs);
    match tx2.sequence_statuses(&context) {
        Err(e) => {
            panic!("tx2_device_statuses: failed: {}", e);
        }
        Ok(statuses) => statuses
            .into_iter()
            .map(|(unit, status)| {
                let tmp = UnitState {
                    unit: u8::from(unit),
                    unit_state: status,
                };
                match serde_wasm_bindgen::to_value(&tmp) {
                    Ok(jsval) => jsval,
                    Err(e) => {
                        panic!("failed to convert {tmp:?} to JsValue: {e}");
                    }
                }
            })
            .collect(),
    }
}

#[derive(Debug)]
enum KeyColour {
    //Orange,
    //Red,
    //Yellow,
    Green,
    //Brown,
    //Gray,
    //Black,
}

impl KeyColour {
    fn css_colour(&self) -> &'static str {
        match self {
            //KeyColour::Orange => "darkorange",
            //KeyColour::Red => "crimson",
            //KeyColour::Yellow => "gold",
            KeyColour::Green => "limegreen",
            //KeyColour::Brown => "brown",
            //KeyColour::Gray => "lightslategrey",
            //KeyColour::Black => "black",
        }
    }
}

#[derive(Debug)]
enum LabelColour {
    //White,
    Black,
}

impl LabelColour {
    fn css_colour(&self) -> &'static str {
        match self {
            //LabelColour::White => "white",
            LabelColour::Black => "black",
        }
    }
}

struct KeyLabel {
    text: &'static [&'static str],
    colour: LabelColour,
}

pub struct KeyPaintError {
    pub msg: String,
}

impl<E: Display> From<E> for KeyPaintError {
    fn from(e: E) -> KeyPaintError {
        KeyPaintError { msg: e.to_string() }
    }
}

trait KeyPainter {
    fn width(&self) -> u32;
    fn height(&self) -> u32;
    fn draw_key(
        &mut self,
        x: u32,
        y: u32,
        halfwidth: u32,
        halfheight: u32,
        colour: &KeyColour,
        label: &KeyLabel,
    ) -> Result<(), KeyPaintError>;
}

#[wasm_bindgen]
pub struct HtmlCanvas2DPainter {
    height: u32,
    width: u32,
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

impl HtmlCanvas2DPainter {
    pub fn new(
        context: web_sys::CanvasRenderingContext2d,
    ) -> Result<HtmlCanvas2DPainter, KeyPaintError> {
        if let Some(canvas) = context.canvas() {
            HtmlCanvas2DPainter::set_up_context_defaults(&context);
            Ok(HtmlCanvas2DPainter {
                height: canvas.height(),
                width: canvas.width(),
                context,
            })
        } else {
            Err("CanvasRenderingContext2d has no associated canvas"
                .to_string()
                .into())
        }
    }

    fn set_up_context_defaults(context: &CanvasRenderingContext2d) {
        context.set_line_cap("round");
        context.set_stroke_style(&("black".into()));
    }

    fn fill_multiline_text(
        &mut self,
        x: f64,
        y: f64,
        lines: &'static [&'static str],
    ) -> Result<(), KeyPaintError> {
        let metrics: Vec<TextMetrics> =
            match lines.iter().map(|s| self.context.measure_text(s)).collect() {
                Ok(v) => v,
                Err(e) => {
                    return Err(format!("measure_text failed: {e:?}").into());
                }
            };
        let max_ascent = metrics
            .iter()
            .map(|m| m.actual_bounding_box_ascent())
            .fold(None, keep_greatest);
        let max_descent = metrics
            .iter()
            .map(|m| m.actual_bounding_box_descent())
            .fold(None, keep_greatest);
        let (a, d) = match (max_ascent, max_descent) {
            (Some(a), Some(d)) => (a, d),
            _ => {
                return Ok(()); // There is no text to draw.
            }
        };
        fn even(n: usize) -> bool {
            n % 2 == 0
        }
        fn yi(i: usize, n: usize, yc: f64, a: f64, d: f64) -> f64 {
            let ashift: f64 = if even(i) { a } else { 0.0 };
            let i_plus_floor_half_n = f64::value_from(i + n / 2).unwrap_or(f64::MAX);
            yc + ashift + i_plus_floor_half_n * (a + d)
        }

        let n = lines.len();
        let total_height: f64 = (a + d) * f64::value_from(n).unwrap_or(f64::MAX);
        let yc = y + (total_height / 2.0);
        for (i, (s, metrics)) in lines.iter().zip(metrics.iter()).enumerate() {
            let text_y = yi(i, n, yc, a, d);
            // This calculation for x assumes Left-to-Right text.
            let text_x: f64 = x - metrics.actual_bounding_box_right() / 2.0;
            if let Err(e) = self.context.fill_text(s, text_x, text_y) {
                return Err(format!("fill_text failed: {e:?}").into());
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
    fn width(&self) -> u32 {
        self.width
    }

    fn height(&self) -> u32 {
        self.height
    }

    fn draw_key(
        &mut self,
        x: u32,
        y: u32,
        halfwidth: u32,
        halfheight: u32,
        colour: &KeyColour,
        label: &KeyLabel,
    ) -> Result<(), KeyPaintError> {
        self.context.set_fill_style(&colour.css_colour().into());
        self.draw_filled_stroked_rect(
            (x - halfwidth).into(),
            (y - halfheight).into(),
            (halfwidth * 2).into(),
            (halfheight * 2).into(),
        );
        self.context
            .set_fill_style(&label.colour.css_colour().into());
        self.fill_multiline_text(x.into(), y.into(), label.text)
    }
}

fn draw_kb<P: KeyPainter>(painter: &mut P) -> Result<(), KeyPaintError> {
    let hw = painter.width() / 2;
    let hh = painter.height() / 2;
    painter.draw_key(
        hw,
        hh,
        hw,
        hh,
        &KeyColour::Green,
        &KeyLabel {
            text: &["N"],
            colour: LabelColour::Black,
        },
    )
}

#[wasm_bindgen]
pub fn draw_keyboard(painter: &mut HtmlCanvas2DPainter) -> Result<(), JsValue> {
    draw_kb(painter).map_err(|e| e.msg.into())
}
