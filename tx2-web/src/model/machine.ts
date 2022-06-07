// This module is a TypeScript interface to the WASM code.
//

let wasm: any;			// the WASM module.

export function set_app_wasm_mod(m: any) {
    wasm = m;
}

export function get_app_wasm_mod(): any {
    return wasm;
}
