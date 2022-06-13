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

type ChangeCallback = (props: IoUnitProps) => void;
type RegisterCallback = (name: string, f: ChangeCallback | null) => void;

export interface IoUnitProps {
    unit: number;
    key: string;
    flag: boolean;
    connected: boolean;
    in_maintenance: boolean;
    name: string;
    text_info: string;
    status: WasmExtendedConnectedUnitStatus | null;
    registerCallback: RegisterCallback;
}

export interface WasmUnitState { // mirrors struct UnitState in WASM (lib.rs)
    unit: number,
    unit_state: WasmExtendedUnitState,
}

export interface AlarmStatusCallback {
    (status: IoUnitProps): void;
}

export class IoController {
    io_status_callbacks: Map<string, ChangeCallback | null>;
    tx2Controller: Tx2Controller;

    constructor(tx2Controller: Tx2Controller) {
        this.io_status_callbacks = new Map<string, ChangeCallback | null>();
        this.tx2Controller = tx2Controller;
    }

    set_io_status_callback(name: string, f: ChangeCallback | null): void {
        this.io_status_callbacks.set(name, f);
    }

    convert_wasm_unit_state_to_props(state: WasmUnitState): IoUnitProps {
        return {
            unit: state.unit,
            key: state.unit.toString(8),
            flag: state.unit_state.flag,
            connected: state.unit_state.connected,
            in_maintenance: state.unit_state.in_maintenance,
            name: state.unit_state.name,
            text_info: state.unit_state.text_info,
            status: state.unit_state.status,
            registerCallback: (name: string, f: ChangeCallback | null) => void (this.io_status_callbacks.set(name, f)),
        };
    }

    allUnitProps(): IoUnitProps[] {
        const statuses = this.tx2Controller.get_device_statuses();
        return Array.from(statuses, this.convert_wasm_unit_state_to_props.bind(this));
    }

    update_status_around(f: ()=>void): void {
        const prev_io_status = this.allUnitProps();
        f();
        this.update_io_status_changes(prev_io_status, this.allUnitProps());
    }

    private update_io_status_changes(prev: IoUnitProps[] | null,
                                     current: IoUnitProps[]): void {
        const performUpdate = (unit_props: IoUnitProps): void => {
            const cb = this.io_status_callbacks.get(unit_props.name);
            if (cb) {
                cb(unit_props);
            }
        };
        current.forEach(performUpdate);
    }
}
