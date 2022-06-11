import React, { Component } from 'react';
import Checkbox from './checkbox';
import styled from 'styled-components';

import { AlarmStatus, AlarmStatusCallback, AlarmControlState } from './controller/alarms'

export interface AlarmControlProps {
  name: string;
  maskable: boolean;
  masked: boolean,
  active: boolean,
  message: string | null,
  setMaskedCallback: (name: string, masked: boolean) => void;
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void;
}

const AlarmRowHeader = styled.th`
  text-align: right;
  border: 1px solid black;
`;
const AlarmCell = styled.td`
  border: 1px solid black;
`;
const MaskedCell = styled(AlarmCell)`
  text-align: center;
`;
const ActiveCell = styled(AlarmCell)`
  text-align: center;
`;

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
	<AlarmRowHeader scope="row">{this.props.name}</AlarmRowHeader>
	<MaskedCell>{this.masked()}</MaskedCell>
	<ActiveCell>{this.yesno(this.state.active)}</ActiveCell>
	<AlarmCell>{this.state.message}</AlarmCell>
      </tr>
    );
  }
}

const AlarmTable = styled.table`
  border-collapse: collapse;
  border: 1px solid black;
  margin: 0.5em;
`;
const AlarmHeader = styled.th`
  border: 1px solid black;
`;

interface AlarmPanelProps {
  alarmStatuses: AlarmStatus[];
  maskedChangeCallback: (name: string, masked: boolean) => void;
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void;
  customStyles: any,
}

interface AlarmPanelState {
}

function make_control(
  name: string,
  alarmStatus: AlarmStatus,
  maskedChangeCallback: (name: string, masked: boolean) => void,
  registerStatusCallback: (name: string, f: AlarmStatusCallback | null) => void,
): JSX.Element {
	return (<AlarmControl
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
      <AlarmTable aria-label="Alarm Status" style={this.props.customStyles}>
	<thead>
	  <tr>
	    <AlarmHeader scope="col">Alarm</AlarmHeader>
	    <AlarmHeader scope="col">Masked</AlarmHeader>
	    <AlarmHeader scope="col">Active</AlarmHeader>
	    <AlarmHeader scope="col">Message</AlarmHeader>
	  </tr>
	</thead>
	<tbody>
	  {alarmControls}
	</tbody>
      </AlarmTable>
    );
  }
}
