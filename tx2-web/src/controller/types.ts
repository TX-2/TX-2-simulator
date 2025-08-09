
// WasmExtendedConnectedUnitStatus mirrors struct ExtendedConnectedUnitStatus in WASM (cpu/src/io.rs)
export interface WasmExtendedConnectedUnitStatus {
    buffer_available_to_cpu: boolean;
    inability: boolean;
    missed_data: boolean;
    special: number;
    mode: number;
}

// WasmExtendedUnitState mirrors struct UnitState in WASM (cpu/src/io.rs)
export interface WasmExtendedUnitState {
    flag: boolean;
    index_value: number;
    connected: boolean;
    in_maintenance: boolean;
    name: string;
    text_info: string;
    status: WasmExtendedConnectedUnitStatus | null;
}

export interface WasmUnitState { // mirrors struct UnitState in WASM (lib.rs)
    unit: number,
    unit_state: WasmExtendedUnitState,
}
