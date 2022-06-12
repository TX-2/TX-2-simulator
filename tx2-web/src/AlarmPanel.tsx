import React, { Component } from 'react';
import Checkbox from './checkbox';
import styles from './styles.scss'

import { AlarmStatus, AlarmStatusCallback, AlarmControlState } from './controller/alarms'

export interface AlarmControlProps {
  name: string;
  maskable: boolean;
  masked: boolean,
  active: boolean,
  message: string | null,
  className: string,
  setMaskedCallback: (name: string, masked: boolean) => void;
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void;
}


function AlarmCell(props: any) {
  return <td>{props.children}</td>;
}

function MaskedCell(props: any) {
  return (<td
    className={styles['alarm-panel__masked']}>
    {props.children}
  </td>);
}

function ActiveCell(props: any) {
  return (
    <td className={styles['alarm-panel__active']}>
      {props.children}
    </td>
    );
}

function MessageCell(props: any) {
  return (
    <td className={styles['alarm-panel__message']}>
      {props.children}
    </td>
    );
}

class AlarmControl extends Component<AlarmControlProps, AlarmControlState> {
  constructor(props: AlarmControlProps) {
    super(props);
    let msg = props.message;
    if (msg == null) {
      msg = ""
      }
    this.state = {
      masked: props.masked,
      active: props.active,
      message: msg,
    }
  }

  componentDidMount() {
    // TODO: should more of this mount/unmount logic go into the
    // controller somehow?
    this.props.registerStatusCallback(this.props.name, this.updateStatus.bind(this));
  }

  componentWillUnmount() {
    this.props.registerStatusCallback(this.props.name, null);
  }

  updateStatus(newAlarmState: AlarmControlState) {
    this.setState(newAlarmState);
  }

  yesno(flag: boolean): string {
    if (flag) {
      return "yes";
    } else {
      return "no";
    }
  }

  handleMaskedChange(e: React.ChangeEvent<HTMLInputElement>) {
    let masked: boolean = e.target.checked;
    this.props.setMaskedCallback(this.props.name, masked);
    this.setState({
      masked: masked,
      active: this.state.active,
      message: this.state.message
    })
  }

  masked(): React.ReactElement {
    if (this.props.maskable) {
      return (<Checkbox
	isChecked={this.state.masked}
	handleChange={this.handleMaskedChange.bind(this)}
	label={""} />);
    } else {
      return <span>never</span>;
    }
  }

  render() {
    return (
      <tr>
	<th scope="row" className={styles['alarm-panel__name']}>{this.props.name}</th>
	<MaskedCell>{this.masked()}</MaskedCell>
	<ActiveCell>{this.yesno(this.state.active)}</ActiveCell>
	<MessageCell>{this.state.message}</MessageCell>
      </tr>
    );
  }
}

interface AlarmPanelProps {
  alarmStatuses: AlarmStatus[];
  maskedChangeCallback: (name: string, masked: boolean) => void;
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void;
}

interface AlarmPanelState {
}

function make_control(
  name: string,
  alarmStatus: AlarmStatus,
  maskedChangeCallback: (name: string, masked: boolean) => void,
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void,
): JSX.Element {
	return (<AlarmControl className={styles['alarm-panel__name']}
		key={name}
		name={name}
		maskable={alarmStatus.maskable}
		masked={alarmStatus.masked}
		active={alarmStatus.active}
		message={alarmStatus.message}
                setMaskedCallback={maskedChangeCallback}
                registerStatusCallback={registerStatusCallback} />);
}


export default class AlarmPanel extends Component<AlarmPanelProps, AlarmPanelState> {
  constructor(props: AlarmPanelProps) {
    super(props);
  }

  render() {
    let alarmControls: JSX.Element[] = this.props.alarmStatuses.map((status) =>
      make_control(status.name, status, this.props.maskedChangeCallback, this.props.registerStatusCallback));
    return (
      <table className={styles['alarm-panel']} aria-label="Alarm Status">
	<thead>
	  <tr>
	    <th className={styles['alarm-panel__name']} scope="col">Alarm</th>
	    <th className={styles['alarm-panel__masked']} scope="col">Masked</th>
	    <th className={styles['alarm-panel__active']} scope="col">Active</th>
	    <th className={styles['alarm-panel__message']} scope="col">Message</th>
	  </tr>
	</thead>
	<tbody>
	  {alarmControls}
	</tbody>
      </table>
    );
  }
}
