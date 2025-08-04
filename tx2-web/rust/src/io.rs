mod keyboard;

use std::collections::BTreeMap;

use js_sys::Array;
use serde::Serialize;
use tracing::{Level, event};
use wasm_bindgen::prelude::*;

use base::Unsigned6Bit;
use cpu::*;

use super::context::make_context;
use super::io::keyboard::Code;
use super::samples::{sample_binary_echo, sample_binary_hello};

pub use keyboard::{
    HtmlCanvas2DPainter, KeyPaintError, SWITCH_TO_FAR, SWITCH_TO_NEAR, draw_keyboard,
};

#[wasm_bindgen]
pub fn tx2_load_tape(
    tx2: &mut Tx2,
    simulated_time: f64,
    elapsed_time_secs: f64,
    data: &[u8],
) -> bool {
    let context = make_context(simulated_time, elapsed_time_secs);
    tx2.mount_tape(&context, data.to_vec()).map_or_else(
        |e: InputEventError| {
            event!(Level::ERROR, "failed to load paper tape: {e}");
            false
        },
        |f: InputFlagRaised| f.into(),
    )
}

pub(crate) struct EmittedCodes {
    first: u8,
    second: Option<u8>,
    far_now_active: bool,
}

fn try_u6_from_u8(x: u8) -> Result<Unsigned6Bit, String> {
    fn failed<E: std::error::Error>(e: E) -> String {
        format!("failed to map a key code into a six-bit number: {e}")
    }
    <Unsigned6Bit as std::convert::TryFrom<u8>>::try_from(x).map_err(failed)
}

impl EmittedCodes {
    fn try_to_u6_vec(&self) -> Result<Vec<Unsigned6Bit>, String> {
        let mut result: Vec<Unsigned6Bit> =
            Vec::with_capacity(if self.second.is_some() { 2 } else { 1 });
        result.push(try_u6_from_u8(self.first)?);
        if let Some(second) = self.second {
            result.push(try_u6_from_u8(second)?);
        }
        Ok(result)
    }
}

pub(crate) fn hit_detection_rgb_to_code(
    far_currently_active: bool,
    r: u8,
    g: u8,
    b: u8,
) -> Result<Option<EmittedCodes>, String> {
    match Code::hit_detection_rgb_to_code(r, g, b) {
        Ok(Some(Code::Far(code))) => Ok(Some(if far_currently_active {
            EmittedCodes {
                first: code,
                second: None,
                far_now_active: true,
            }
        } else {
            EmittedCodes {
                first: SWITCH_TO_FAR,
                second: Some(code),
                far_now_active: true,
            }
        })),
        Ok(Some(Code::Near(code))) => Ok(Some(if far_currently_active {
            EmittedCodes {
                first: SWITCH_TO_NEAR,
                second: Some(code),
                far_now_active: false,
            }
        } else {
            EmittedCodes {
                first: code,
                second: None,
                far_now_active: false,
            }
        })),
        Ok(None) => Ok(None),
        Ok(Some(Code::Unknown)) => {
            event!(
                Level::DEBUG,
                "the user hit a key whose key code we don't know"
            );
            Ok(None)
        }
        Err(e) => Err(e),
    }
}

#[wasm_bindgen]
pub struct KeystrokeOutcome {
    consumed: bool,
    flag_raised: bool,
    far_keyboard_is_active: bool,
}

#[wasm_bindgen]
impl KeystrokeOutcome {
    #[wasm_bindgen(getter)]
    pub fn consumed(&self) -> bool {
        self.consumed
    }

    #[wasm_bindgen(getter)]
    pub fn flag_raised(&self) -> bool {
        self.flag_raised
    }

    #[wasm_bindgen(getter)]
    pub fn far_keyboard_is_active(&mut self) -> bool {
        self.far_keyboard_is_active
    }
}

#[wasm_bindgen]
pub fn tx2_lw_keyboard_click(
    tx2: &mut Tx2,
    simulated_time: f64,
    elapsed_time_secs: f64,
    unit: u8,
    far_currently_active: bool,
    rgb: &js_sys::Uint8ClampedArray,
) -> KeystrokeOutcome {
    let context = make_context(simulated_time, elapsed_time_secs);
    match hit_detection_rgb_to_code(
        far_currently_active,
        rgb.at(0).unwrap_or(0),
        rgb.at(1).unwrap_or(0),
        rgb.at(2).unwrap_or(0),
    ) {
        Ok(Some(codes)) => match try_u6_from_u8(unit) {
            Ok(unit) => match codes.try_to_u6_vec() {
                Err(e) => {
                    event!(
                        Level::ERROR,
                        "tx2_lw_keyboard_click: failed to convert input key code: {e}"
                    );
                    KeystrokeOutcome {
                        consumed: false,
                        flag_raised: false,
                        far_keyboard_is_active: codes.far_now_active,
                    }
                }
                Ok(data) => match tx2.lw_input(&context, unit, &data) {
                    Ok((consumed, flag_raise)) => KeystrokeOutcome {
                        consumed,
                        flag_raised: flag_raise.into(),
                        far_keyboard_is_active: codes.far_now_active,
                    },
                    Err(e) => {
                        event!(
                            Level::ERROR,
                            "tx2_lw_keyboard_click: failed to accept input key: {e}"
                        );
                        KeystrokeOutcome {
                            consumed: false,
                            flag_raised: false,
                            far_keyboard_is_active: codes.far_now_active,
                        }
                    }
                },
            },
            Err(_) => {
                event!(
                    Level::WARN,
                    "tx2_lw_keyboard_click: unit {unit:o} is out of range"
                );
                KeystrokeOutcome {
                    consumed: false,
                    flag_raised: false,
                    far_keyboard_is_active: codes.far_now_active,
                }
            }
        },
        Ok(None) => {
            // Click on something that wasn't a key.
            KeystrokeOutcome {
                consumed: true,
                flag_raised: false,
                far_keyboard_is_active: far_currently_active,
            }
        }
        Err(_) => KeystrokeOutcome {
            consumed: true,
            flag_raised: false,
            far_keyboard_is_active: far_currently_active,
        },
    }
}

#[wasm_bindgen]
pub fn get_builtin_sample_tape(sample_name: &str) -> Result<Vec<u8>, String> {
    match sample_name {
        "echo" => Ok(sample_binary_echo()),
        "hello" => Ok(sample_binary_hello()),
        _ => Err(format!("unknown sample file '{sample_name}'")),
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
            panic!("tx2_device_statuses: failed: {e}");
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
