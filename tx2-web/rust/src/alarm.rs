use std::collections::BTreeMap;

use wasm_bindgen::prelude::*;

use cpu::*;

#[wasm_bindgen]
pub fn tx2_unmasked_alarm_active(tx2: &Tx2) -> bool {
    tx2.unmasked_alarm_active()
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
