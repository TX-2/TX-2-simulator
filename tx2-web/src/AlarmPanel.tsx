import React, { Component } from 'react';
import Checkbox from './checkbox';
import styled from 'styled-components';
import { set_alarm_masked, set_alarm_status_callback } from './model/machine'

export interface AlarmControlProps {
  name: string;
  maskable: boolean;
  masked: boolean,
  active: boolean,
  message: string | null,
}
interface AlarmControlState {
  masked: boolean;
  active: boolean;
  message: string;
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

  yesno(flag: boolean): string {
    if (flag) {
      return "yes";
    } else {
      return "no";
    }
  }

  handleMaskedChange(e: React.ChangeEvent<HTMLInputElement>) {
    let masked: boolean = e.target.checked;
    set_alarm_masked(this.props.name, masked);
    this.setState({
      masked: masked,
      active: this.state.active,
      message: this.state.message,
    });
  }

  update_from_model(new_alarm_state: AlarmControlState) {
    console.log("AlarmControl: updating from ", {new_alarm_state});
    this.setState({
      masked: new_alarm_state.masked,
      active: new_alarm_state.active,
      message: new_alarm_state.message,
    })
  }

  componentDidMount() {
    set_alarm_status_callback(this.props.name, this.update_from_model.bind(this))
  }

  componentWillUnmount() {
    set_alarm_status_callback(this.props.name, null)
  }

  masked(): React.ReactElement {
    if (this.props.maskable) {
      return <Checkbox
	isChecked={this.state.masked}
	handleChange={this.handleMaskedChange.bind(this)}
	label={""} />;
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
`;
const AlarmHeader = styled.th`
  border: 1px solid black;
`;

interface AlarmPanelProps {
  info: AlarmControlProps[];
}
interface AlarmPanelState {
}
export default class AlarmPanel extends Component<AlarmPanelProps, AlarmPanelState> {
  constructor(props: AlarmPanelProps) {
    super(props);
  }

  render() {
    const alarmControls = this.props.info.map((info) =>
      <AlarmControl
	key={info.name}
	name={info.name}
	maskable={info.maskable}
	masked={info.masked}
	active={info.active}
	message={info.message}
      />
    );
    return (
      <AlarmTable>
	<caption>Alarm Status:</caption>
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
