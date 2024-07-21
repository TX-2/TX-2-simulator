
import { Grid, GridItemProps } from '@react-css/grid';
import { AlarmController } from 'controller/alarms';
import AlarmPanel from './AlarmPanel';
import Checkbox from './checkbox';
import { IoController } from 'controller/io';
import { IoPanel } from './IoPanel';
import { LincolnWriter } from './LincolnWriter';
import React from 'react';
import styles from './styles.scss';
import TapeLoadModal from './TapeLoadModal';
import { Tx2Controller } from 'controller/tx2';

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
      <button id="tapeLoadBtn" onClick={openModal}>Mount Paper Tape</button>
      <button id="codaboTSRBtn" onClick={tx2Controller.codabo.bind(tx2Controller)}>CODABO (TSR)</button>
      <Checkbox label="Run" handleChange={handleChangeRun.bind(this)} isChecked={isRunning} />
      <TapeLoadModal
        modalIsOpen={modalIsOpen}
        closeModal={closeModal} loadTape={loadTape} loadSample={loadSample}/>
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
    className={styles['gridbox']}
  >{props.children}</Grid.Item>
  );
}


export const MainGrid = (props: MainGridProps) => (
  <div>
    <Grid
      gap="10px"
      rows="auto auto auto auto"
    >
  <Box column="1" row="1">
        <details open>
          <summary>Instructions</summary>
          <p>Here are some getting-started instructions.</p>
          <ol>
            <li> Press &quot;Mount Paper Tape&quot; and press the button to load the &lsquo;hello&rsquo; sample file.</li>
            <li> Press the CODABO (TSR) button.</li>
          </ol>
          <p>
            Presently you should see some output.
            You can <a href="https://tx-2.github.io/">find out more about
              the simulator project on our website</a> or <a
                href="https://github.com/TX-2/TX-2-simulator">take a
                look at the source code</a>.
          </p>
        </details>
      </Box>
      <Box column="1" row="2">
        <Buttons
          changeRunCallback={props.tx2Controller.changeRun.bind(props.tx2Controller)}
          tx2Controller={props.tx2Controller}
          isClockRunning={props.tx2Controller.isClockRunning()}
          loadTape={props.loadTape}
          loadSample={props.loadSample}
        />
      </Box>
      <Box column="1" row="3">
        <div className={styles['main-grid-flexbox']}>
          <details className="alarm-details">
            <summary>Alarms</summary>
            <AlarmPanel
              alarmStatuses={props.alarmController.all_alarm_info()}
              maskedChangeCallback={props.alarmController.set_alarm_masked.bind(props.alarmController)}
              registerStatusCallback={props.alarmController.set_alarm_status_callback.bind(props.alarmController)}
            />
          </details>
          <details className="io-details">
            <summary>I/O</summary>
            <IoPanel ioController={props.ioController} />
          </details>
        </div>
      </Box>
      <Box column="1" row="4" className={styles['lw__box']}>
        <LincolnWriter
          inputUnit={0o65}
          outputUnit={0o66}
          tx2Controller={props.tx2Controller} />
      </Box>
    </Grid>
  </div>
);
