// This module is a TypeScript interface to the WASM code.
//

let wasm;			// the WASM module.

export function set_app_wasm_mod(m) {
    wasm = m;
}

export function get_app_wasm_mod() {
    return wasm;
}
