import React, { Component } from 'react';
import { IoController, IoUnitProps } from './controller/io'
import styled from 'styled-components';

function choose(flag: boolean, noval: string, yesval: string): string {
  if (flag) {
    return yesval;
  } else {
    return noval;
  }
}

function yesno(flag: boolean): string {
  return choose(flag, "no", "yes");
}

function yesnoblank(nonblank: boolean, flag: boolean | null | undefined): string {
  return chooseblank(nonblank && flag != null, flag, "no", "yes");
}

function chooseblank(nonblank: boolean, flag: boolean | null | undefined, noval: string, yesval: string): string {
  const blank = "";
  if (!nonblank || (flag === undefined || flag === null)) {
    return blank;
  } else {
    if (flag) {
      return yesval;
    } else {
      return noval;
    }
  }
}

const IoRowHeader = styled.th`
  text-align: right;
  border: 1px solid black;
`;
const IoColHeader = styled.th`
  text-align: right;
  border: 1px solid black;
`;

const IoCell = styled.td`
  border: 1px solid black;
`;

interface OctalNumberCellProps {
  value: number | undefined | null;
  width: number;
}

function OctalNumberCell(props: OctalNumberCellProps) {
  if (props.value === undefined || props.value === null) {
    return <IoCell></IoCell>;
  } else {
    return (<IoCell>{props.value.toString(8).padStart(props.width, '0')}</IoCell>);
  }
}

interface IoUnitHeaderProps {
  value: number;
}

function IoUnitHeader(props: IoUnitHeaderProps) {
  return (<IoRowHeader>{props.value.toString(8).padStart(2, '0')}</IoRowHeader>);
}


export interface EmptyState {
}

export class IoUnitStatusRow extends Component<IoUnitProps, IoUnitProps> {

  constructor(props: IoUnitProps) {
    super(props);
    this.state = props;
  }

  componentDidMount() {
    // TODO: should more of this mount/unmount logic go into the
    // controller somehow?
    this.props.registerCallback(this.props.name, this.updateStatus.bind(this));
  }

  componentWillUnmount() {
    this.props.registerCallback(this.props.name, null);
  }

  updateStatus(newprops: IoUnitProps): void {
    this.setState(newprops);
  }

  render() {
    let state = this.state;
    return (<tr>
      <IoUnitHeader value={this.props.unit} />
      <IoCell>{this.state.name}</IoCell>
      <IoCell>{choose(this.state.flag, "down", "up")}</IoCell>
      <IoCell>{yesno(this.state.connected)}</IoCell>
      <IoCell>{chooseblank(this.state.connected, this.state.status?.buffer_available_to_cpu, "busy", "free")}</IoCell>
      <IoCell>{yesno(this.state.in_maintenance)}</IoCell>
      <IoCell>{yesnoblank(!!this.state.connected, this.state.status?.inability)}</IoCell>
      <IoCell>{yesnoblank(!!this.state.connected, this.state.status?.missed_data)}</IoCell>
      <OctalNumberCell value={this.state.status?.special} width={4} />
      <OctalNumberCell value={this.state.status?.mode} width={4} />
      <IoCell>{this.state.text_info}</IoCell>
    </tr>
    );
  }
}

const IoPanelTable = styled.table`
  margin: 0.5em;
  border-collapse: collapse;
  border: 1px solid black;
`;

export interface IoUnitStatusPanelProps {
  ioController: IoController,
  customStyles: any,
  //units: IoUnitStatusRowProps[];
}

function nvl(input: any | null, default_value: any): any {
  if (input == null) {
    return default_value;
  } else {
    return input;
  }
}


export class IoPanel extends Component<IoUnitStatusPanelProps, EmptyState> {
  constructor(props: IoUnitStatusPanelProps) {
    super(props);
  }

  render() {
    let unitPropsArray: IoUnitProps[] = this.props.ioController.allUnitProps();
    let rows: React.ReactNode[] = unitPropsArray.map((props) =>
      <IoUnitStatusRow
	unit={props.unit}
	key={props.key}
	flag={props.flag}
	connected={props.connected}
	in_maintenance={props.in_maintenance}
	name={props.name}
	text_info={props.text_info}
	status={props.status}
	registerCallback={props.registerCallback}
      />);
    return (
      <IoPanelTable style={this.props.customStyles}>
	<thead>
	  <tr>
	    <IoColHeader scope="col">Unit</IoColHeader>
	    <IoColHeader scope="col">Name</IoColHeader>
	    <IoColHeader scope="col">Flag</IoColHeader>
	    <IoColHeader scope="col">Connected</IoColHeader>
	    <IoColHeader scope="col">Status</IoColHeader>
	    <IoColHeader scope="col">Maintenance</IoColHeader>
	    <IoColHeader scope="col">Inability</IoColHeader>
	    <IoColHeader scope="col">Missed Data</IoColHeader>
	    <IoColHeader scope="col">Special</IoColHeader>
	    <IoColHeader scope="col">Mode</IoColHeader>
	    <IoColHeader scope="col">Info</IoColHeader>
	  </tr>
	</thead>
	<tbody>
	  {rows}
	</tbody>
      </IoPanelTable>
    );
  }
}
