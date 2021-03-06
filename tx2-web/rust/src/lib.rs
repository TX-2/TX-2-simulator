#![deny(unreachable_pub)]
#![deny(unsafe_code)]
#![deny(unused_crate_dependencies)]

use std::collections::BTreeMap;
use std::time::Duration;

mod samples;
mod utils;

use base::charset::{Colour, DescribedChar, LincolnChar, LincolnState, Script};
use base::Unsigned6Bit;
use cpu::Context;
use cpu::*;

use float_next_after::NextAfter;
use js_sys::Array;
use samples::sample_binary_hello;
use serde::Serialize;
use tracing::{event, Level};
use wasm_bindgen::prelude::*;
use web_sys::{Document, Window};

#[wasm_bindgen(start)]
pub fn start() -> Result<(), JsValue> {
    utils::set_panic_hook();
    Ok(())
}

fn try_log_level_from_str(log_level: &str) -> Result<Level, String> {
    match log_level {
        "trace" => Ok(Level::TRACE),
        "debug" => Ok(Level::DEBUG),
        "info" => Ok(Level::INFO),
        "warn" => Ok(Level::WARN),
        "error" => Ok(Level::ERROR),
        invalid => Err(format!("invalid log level '{invalid}'")),
    }
}

#[wasm_bindgen]
pub fn init(log_level: &str) -> Result<(), JsValue> {
    tracing_wasm::set_as_global_default_with_config(
        tracing_wasm::WASMLayerConfigBuilder::new()
            .set_max_level(try_log_level_from_str(log_level)?)
            .build(),
    );
    event!(
        Level::INFO,
        "init: tracing iniialised (max level is {log_level})"
    );
    Ok(())
}

fn make_context(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Context {
    Context {
        simulated_time: Duration::from_secs_f64(simulated_system_time_secs),
        real_elapsed_time: Duration::from_secs_f64(elapsed_time_secs),
    }
}

#[wasm_bindgen]
pub fn create_tx2(simulated_system_time_secs: f64, elapsed_time_secs: f64) -> Tx2 {
    let mem_config = MemoryConfiguration {
        with_u_memory: false,
    };
    let context = make_context(simulated_system_time_secs, elapsed_time_secs);
    let panic_on_unmasked_alarm = cpu::PanicOnUnmaskedAlarm::No;
    Tx2::new(&context, panic_on_unmasked_alarm, &mem_config)
}

#[wasm_bindgen]
pub fn tx2_next_simulated_tick(tx2: &Tx2) -> f64 {
    let next = tx2.next_tick();
    // We use next_after to round f up slightly to ensure that the
    // tick time used by the next JS call to tick() is actually a
    // different time to the current tick.
    let f = next.as_secs_f64().next_after(std::f64::INFINITY);
    event!(
        Level::TRACE,
        "tx2_next_simulated_tick: next={next:?}, f={f:?}"
    );
    f
}

#[wasm_bindgen]
pub fn tx2_unmasked_alarm_active(tx2: &Tx2) -> bool {
    tx2.unmasked_alarm_active()
}

fn window() -> Window {
    web_sys::window().expect("no global window exists")
}

fn document() -> Document {
    window()
        .document()
        .expect("should have a document on the window")
}

fn generate_html_for_char(uch: char, attributes: &LincolnState, _advance: bool) -> String {
    let colour_class = match attributes.colour {
        Colour::Black => "lw-black",
        Colour::Red => "lw-red",
    };
    let (script_open, script_close) = match attributes.script {
        Script::Normal => ("", ""),
        Script::Super => ("<sup>", "</sup>"),
        Script::Sub => ("<sub>", "</sub>"),
    };
    // TODO: By recalling existing colour and script information we
    // could save on olume of output here.
    format!("<span class=\"{colour_class}\">{script_open}{uch}{script_close}</span>")
}

fn display_lw_unit_output_event(unit: Unsigned6Bit, ch: DescribedChar) {
    event!(
        Level::INFO,
        "display_lw_unit_output_event: handling output event for LW unit {unit:?}"
    );
    let current_line_element_id = format!("lw{:o}-current-line", unit);
    let current_line_el = document()
        .get_element_by_id(&current_line_element_id)
        .expect("LW current line element is missing from HTML document");
    let mut current_line_text = current_line_el.inner_html();
    match ch {
        DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar('\r'),
            ..
        } => {
            event!(Level::INFO, "LW: processing a carriage return");
            let history_element_id = format!("lw{:o}-history", unit);
            let history_el = document()
                .get_element_by_id(&history_element_id)
                .expect("LW history element is missing from HTML document");
            // Append the current line to the history.
            let mut history_text = history_el.inner_html();
            history_text.push_str(&current_line_text);
            history_text.push_str("<br/>\r\n");
            history_el.set_inner_html(&history_text);
            // Clear the current line.
            current_line_el.set_inner_html("");
        }
        DescribedChar {
            base_char: LincolnChar::Unprintable(_),
            ..
        } => {
            // We don't print unprintable characters.
        }
        DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar(uch),
            attributes,
            advance,
            unicode_representation: _,
        } => {
            let s: String = generate_html_for_char(uch, &attributes, advance);
            current_line_text.push_str(&s);
            current_line_el.set_inner_html(&current_line_text);
        }
    }
}

fn display_output_event(output_event: OutputEvent) {
    match output_event {
        OutputEvent::LincolnWriterPrint { unit, ch } => display_lw_unit_output_event(unit, ch),
    }
}

#[wasm_bindgen]
pub fn tx2_do_tick(tx2: &mut Tx2, simulated_time: f64, real_elapsed_time: f64) {
    let context = make_context(simulated_time, real_elapsed_time);
    event!(
        Level::TRACE,
        "tx2_do_tick: simulated_time={simulated_time:?}, real_elapsed_time={real_elapsed_time:?}, context={context:?}"
    );
    match tx2.tick(&context) {
        Ok(Some(output)) => {
            event!(
                Level::INFO,
                "tx2_do_tick: handling output event for {output:?}"
            );
            display_output_event(output);
        }
        Ok(None) => (),
        Err(e) => {
            event!(Level::ERROR, "New unmasked TX-2 alarm: {:?}", e);
        }
    }
}

#[wasm_bindgen]
pub fn tx2_codabo(tx2: &mut Tx2, simulated_time: f64, elapsed_time_secs: f64) {
    event!(Level::INFO, "codabo");
    let context = make_context(simulated_time, elapsed_time_secs);
    if let Err(e) = tx2.codabo(&context, &ResetMode::ResetTSP) {
        panic!("codabo failed: {}", e);
    }
    tx2.set_next_execution_due(context.simulated_time, Some(context.simulated_time));
    tx2.set_run_mode(RunMode::Running);
}

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

#[wasm_bindgen]
pub fn get_alarm_statuses(tx2: &Tx2) -> Result<JsValue, String> {
    let alarm_status = tx2.get_alarm_statuses();
    match serde_wasm_bindgen::to_value(&alarm_status) {
        Ok(val) => {
            //event!(
            //    Level::DEBUG,
            //    "get_alarm_statuses: success result is {:?}",
            //    &val
            //);
            Ok(val)
        }
        Err(e) => {
            //event!(Level::DEBUG, "get_alarm_statuses: error result is {:?}", &e);
            Err(e.to_string())
        }
    }
}

#[wasm_bindgen]
pub fn drain_alarm_changes(tx2: &mut Tx2) -> Result<JsValue, String> {
    let change_map: BTreeMap<String, AlarmStatus> = tx2
        .drain_alarm_changes()
        .into_iter()
        .map(|(kind, status)| (kind.to_string(), status))
        .collect();
    serde_wasm_bindgen::to_value(&change_map).map_err(|e| e.to_string())
}

#[wasm_bindgen]
pub fn set_alarm_masked(tx2: &mut Tx2, alarm_name: &str, masked: bool) -> Result<(), String> {
    match AlarmKind::try_from(alarm_name) {
        Ok(kind) => tx2
            .set_alarm_masked(kind, masked)
            .map_err(|e| e.to_string()),
        Err(e) => Err(e.to_string()),
    }
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
