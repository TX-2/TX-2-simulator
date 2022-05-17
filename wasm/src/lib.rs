mod utils;

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}

#[wasm_bindgen]
pub fn greet(whom: &str) {
    alert(format!("Hello, {whom}!").as_str());
}

#[wasm_bindgen]
pub fn set_panic_hook() {
    utils::set_panic_hook();
}
