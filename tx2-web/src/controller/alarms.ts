import { drain_alarm_changes, get_alarm_statuses, set_alarm_masked, Tx2 } from '../../build/tx2_web';

export interface AlarmStatus {
    name: string,
    maskable: boolean,
    masked: boolean,
    active: boolean,
    message: string,
}

export interface AlarmStatusByAlarmName {
    [name: string]: AlarmStatus,
}

export interface AlarmStatusCallback {
    (status: AlarmControlState): void;
}

export interface AlarmControlState {
  masked: boolean;
  active: boolean;
  message: string;
}

interface AlarmStatusCallbackByName {
    [index: string]: AlarmStatusCallback | null
}

interface WasmAlarmStatus {
    name: string,
    maskable: boolean,
    masked: boolean,
    active: boolean,
    message: string,
}

export class AlarmController {
    alarm_status_callbacks: AlarmStatusCallbackByName;
    tx2: Tx2;

    constructor(tx2: Tx2) {
        this.tx2 = tx2;
        this.alarm_status_callbacks = {};
    }

    // TODO: The binding between this callback and the properties of
    // AlarmPanel happens in MainGrid.tsx, at the point where the
    // AlarmPanel is created.  But this looks to me like too much of
    // the internals of AlarmPanel being exposed to MainGrid.
    set_alarm_status_callback(name: string, f: AlarmStatusCallback | null): void {
        this.alarm_status_callbacks[name] = f;
    }

    update_status() {
        const changes = drain_alarm_changes(this.tx2) as Map<string, AlarmStatus>;
	changes.forEach((current_status: AlarmStatus, alarm_name: string) => {
            const callback = this.alarm_status_callbacks[alarm_name];
            if (callback != null) {
                callback(current_status);
            }
	});
    }

    private alarm_status_by_alarm_name(): AlarmStatusByAlarmName {
        // TODO: is this function used?
        const alarm_status: AlarmStatusByAlarmName = {};
        this.all_alarm_info().forEach((st) => {
            alarm_status[st.name] = st;
        });
        return alarm_status;
    }

    all_alarm_info(): AlarmStatus[] {
        function wasm_alarm_status_to_alarm_status(wasm_status: WasmAlarmStatus): AlarmStatus {
            return {
                name: wasm_status.name,
                maskable: wasm_status.maskable,
                masked: wasm_status.masked,
                active: wasm_status.active,
                message: wasm_status.message
            };
        }
	const statuses = get_alarm_statuses(this.tx2) as WasmAlarmStatus[];
	return statuses.map(wasm_alarm_status_to_alarm_status);
    }

    set_alarm_masked(alarm_name: string, masked: boolean): void {
        // TODO: error handling of failure in set_alarm_masked
        set_alarm_masked(this.tx2, alarm_name, masked);
    }
}
