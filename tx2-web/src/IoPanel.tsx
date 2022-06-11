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
  console.log("OctalNumberCellProps", {props});
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

export class IoUnitStatusRow extends Component<IoUnitProps, EmptyState> {
  constructor(props: IoUnitProps) {
    super(props);
  }

  render() {
    let pro = this.props;
    console.log("IoUnitStatusRowProps", {pro});
    return (<tr>
      <IoUnitHeader value={this.props.unit} />
      <IoCell>{this.props.name}</IoCell>
      <IoCell>{choose(this.props.flag, "down", "up")}</IoCell>
      <IoCell>{yesno(this.props.connected)}</IoCell>
      <IoCell>{chooseblank(this.props.connected, this.props.status?.buffer_available_to_cpu, "busy", "free")}</IoCell>
      <IoCell>{yesno(this.props.in_maintenance)}</IoCell>
      <IoCell>{yesnoblank(!!this.props.connected, this.props.status?.inability)}</IoCell>
      <IoCell>{yesnoblank(!!this.props.connected, this.props.status?.missed_data)}</IoCell>
      <OctalNumberCell value={this.props.status?.special} width={4} />
      <OctalNumberCell value={this.props.status?.mode} width={4} />
      <IoCell>{this.props.text_info}</IoCell>
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
