mod keyboard;

use std::collections::BTreeMap;

use js_sys::Array;
use serde::Serialize;
use wasm_bindgen::prelude::*;

use cpu::*;

use crate::context::make_context;
use crate::samples::sample_binary_hello;

pub use keyboard::{draw_keyboard, HtmlCanvas2DPainter, KeyPaintError};

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
