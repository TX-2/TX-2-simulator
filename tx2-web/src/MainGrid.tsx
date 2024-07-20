import { Grid, GridItemProps } from '@react-css/grid';
import { AlarmController } from 'controller/alarms';
import AlarmPanel from './AlarmPanel';
import Checkbox from './checkbox';
import { Instructions } from './Instructions';
import { IoController } from 'controller/io';
import { IoPanel } from './IoPanel';
import { LincolnWriter } from './LincolnWriter';
import React from 'react';
import TapeLoadModal from './TapeLoadModal';
import { Tx2Controller } from 'controller/tx2';
import styles from './styles.scss'

interface ButtonsProps {
  changeRunCallback(run: boolean): void,
  tx2Controller: Tx2Controller,
  isClockRunning: boolean,
  loadTape: (bytes: Uint8Array) => void,
  loadSample: (name: string) => void,
}

const Buttons = ({ changeRunCallback, tx2Controller, isClockRunning, loadTape, loadSample }: ButtonsProps) => {
  const [modalIsOpen, setIsOpen] = React.useState(false);
  const [isRunning, setIsRunning] = React.useState(isClockRunning);

  function openModal() {
    setIsOpen(true);
  }

  function closeModal() {
    setIsOpen(false);
  }

  React.useEffect(() => {
    tx2Controller.setRunChangeCallback(setIsRunning);
    return function cleanup() {
      tx2Controller.unsetRunChangeCallback()
    }
  });

  function handleChangeRun(e: React.ChangeEvent<HTMLInputElement>) {
    const run = !!e.target.checked;
    changeRunCallback(run);
  }

  return (
    <div>
      <TapeLoadModal
        modalIsOpen={modalIsOpen}
        closeModal={closeModal} loadTape={loadTape} loadSample={loadSample}/>
      <Grid gap="2px" columns="auto" rows="min-content min-content auto">
      <Grid.Item><button id="tapeLoadBtn" onClick={openModal}>Mount Paper Tape</button></Grid.Item>
      <Grid.Item><button id="codaboTSRBtn"
        onClick={tx2Controller.codabo.bind(tx2Controller)}>CODABO (TSR)</button></Grid.Item>
      <Grid.Item><Checkbox label="Run" handleChange={handleChangeRun.bind(this)} isChecked={isRunning} /></Grid.Item>
      </Grid>
    </div>
  );
};

interface MainGridProps {
  tx2Controller: Tx2Controller,
  alarmController: AlarmController,
  ioController: IoController,
  loadTape: (bytes: Uint8Array) => void,
  loadSample: (name: string) => void,
}

function Box(props: GridItemProps) {
  return (<Grid.Item
    row={props.row}
    column={props.column}
    style={{ backgroundColor: "lightgray", color: "black", borderRadius: "5px", padding: "10px", ...props.style}}
  >{props.children}</Grid.Item>
  );
}


export const MainGrid = (props: MainGridProps) => (
  <div>
    <Grid
      gap="10px"
      columns="1fr 9fr"
      rows="auto auto 40ex"
    >
      <Box column="1 / span 3" row="1" style={{overflowY: "scroll"}}>
        <Instructions /></Box>
      <Box column="1 / span 3" row="2">
        <div className="main-grid-flexbox">
          <details className="alarm-details">
            <summary>Alarms</summary>
            <AlarmPanel
              alarmStatuses={props.alarmController.all_alarm_info()}
              maskedChangeCallback={props.alarmController.set_alarm_masked.bind(props.alarmController)}
              registerStatusCallback={props.alarmController.set_alarm_status_callback.bind(props.alarmController)}
            />
          </details>
          <details className="io-details" open>
            <summary>I/O</summary>
            <IoPanel ioController={props.ioController} />
          </details>
        </div>
      </Box>
      <Box column="1" row="3">
        <Buttons
          changeRunCallback={props.tx2Controller.changeRun.bind(props.tx2Controller)}
          tx2Controller={props.tx2Controller}
          isClockRunning={props.tx2Controller.isClockRunning()}
          loadTape={props.loadTape}
          loadSample={props.loadSample}
        />
      </Box>
      <Box column="2" row="3" className={styles['lw__container']}>
        <LincolnWriter
          inputUnit={0o65}
          outputUnit={0o66}
          tx2Controller={props.tx2Controller} />
      </Box>
    </Grid>
  </div>
);
