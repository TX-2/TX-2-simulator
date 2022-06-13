import React, { Component } from 'react';
import { IoController, IoUnitProps } from './controller/io'
import styles from './styles.scss'

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

interface OctalNumberCellProps {
  value: number | undefined | null;
  digits: number;
}

function OctalNumberCell(props: OctalNumberCellProps) {
  var content: string = "";
  if (props.value === undefined || props.value === null) {
    content = "";
  } else {
    content = props.value.toString(8).padStart(props.digits, '0');
  }
  return (<IoCell>{content}</IoCell>);
}

interface IoUnitHeaderProps {
  value: number;
}

function IoUnitHeader({value}: IoUnitHeaderProps) {
  return (<th
    scope="row"
    className={styles['io-panel']}
  >{value.toString(8).padStart(2, '0')}</th>
  );
}

function IoCell(props: any) {
  return <td className={styles['io-panel']}>{props.children}</td>;
}

function IoColHeader(props: any) {
  return <th
    scope="col"
    className={styles['io-panel']}>
    {props.children}
  </th>;
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
      <OctalNumberCell value={this.state.status?.special} digits={4} />
      <OctalNumberCell value={this.state.status?.mode} digits={4} />
      <IoCell>{this.state.text_info}</IoCell>
    </tr>
    );
  }
}

function IoPanelTable(props: any) {
  return (<table className={styles['io-panel']}>{props.children}</table>);
}

export interface IoUnitStatusPanelProps {
  ioController: IoController,
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
      <IoPanelTable>
        <thead>
          <tr>
            <IoColHeader>Unit</IoColHeader>
            <IoColHeader>Name</IoColHeader>
            <IoColHeader>Flag</IoColHeader>
            <IoColHeader>Connected</IoColHeader>
            <IoColHeader>Status</IoColHeader>
            <IoColHeader>Maintenance</IoColHeader>
            <IoColHeader>Inability</IoColHeader>
            <IoColHeader>Missed Data</IoColHeader>
            <IoColHeader>Special</IoColHeader>
            <IoColHeader>Mode</IoColHeader>
            <IoColHeader>Info</IoColHeader>
          </tr>
        </thead>
        <tbody>
          {rows}
        </tbody>
      </IoPanelTable>
    );
  }
}
