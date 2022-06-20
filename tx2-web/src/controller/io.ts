import { WasmExtendedConnectedUnitStatus, WasmUnitState } from './types'
import { Tx2Controller } from './tx2'


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

    update_status() {
        const changes: Map<number, WasmUnitState> = this.tx2Controller.drain_device_status_changes();
        this.update_io_status_changes(changes);
    }

    private update_io_status_changes(changes: Map<number, WasmUnitState>): void {
        const performUpdate = (state: WasmUnitState): void => {
            const cb = this.io_status_callbacks.get(state.unit_state.name);
            if (cb) {
                const unit_props = this.convert_wasm_unit_state_to_props(state);
                cb(unit_props);
            }
        };
	changes.forEach(performUpdate);
    }
}
