import { get_app_wasm_mod } from '../model/machine'
import { Tx2Controller } from './tx2'


// WasmExtendedConnectedUnitStatus mirrors struct ExtendedConnectedUnitStatus in WASM (cpu/src/io.rs)
interface WasmExtendedConnectedUnitStatus {
    buffer_available_to_cpu: boolean;
    inability: boolean;
    missed_data: boolean;
    special: number;
    mode: number;
}

// WasmExtendedUnitState mirrors struct UnitState in WASM (cpu/src/io.rs)
interface WasmExtendedUnitState {
    flag: boolean;
    connected: boolean;
    in_maintenance: boolean;
    name: string;
    text_info: string;
    status: WasmExtendedConnectedUnitStatus | null;
}

export interface IoUnitProps {
    unit: number;
    key: string;
    flag: boolean;
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

function convert_wasm_unit_state_to_props(state: WasmUnitState): IoUnitProps {
    return {
	unit: state.unit,
	key: state.unit.toString(8),
	flag: state.unit_state.flag,
	connected: state.unit_state.connected,
	in_maintenance: state.unit_state.connected,
	name: state.unit_state.name,
	text_info: state.unit_state.text_info,
	status: state.unit_state.status
    };
}

export class IoController {
    tx2Controller;

    constructor(tx2Controller) {
	this.tx2Controller = tx2Controller;
    }

    allUnitProps(): IoUnitProps[] {
	let statuses = this.tx2Controller.get_device_statuses();
	return Array.from(statuses, convert_wasm_unit_state_to_props);
    }
}
