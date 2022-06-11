import React, { FunctionComponent, ReactElement } from 'react';
import { Instructions } from './Instructions';
import Checkbox from './checkbox';
import { LincolnWriter } from './LincolnWriter';
import { IoPanel } from './IoPanel';
import AlarmPanel, { AlarmControlProps } from './AlarmPanel';
import TapeLoadModal from './TapeLoadModal';
import Flex from './Flex';
import { Tx2Controller } from 'controller/tx2';
import { AlarmController } from 'controller/alarms';
import { IoController } from 'controller/io';
import { Grid } from '@react-css/grid';

interface ButtonsProps {
  changeRunCallback(run: boolean): void,
  tx2Controller: Tx2Controller,
  isClockRunning: boolean,
  loadTape: (Uint8Array) => void,
}

const Buttons = ({ changeRunCallback, tx2Controller, isClockRunning, loadTape }: ButtonsProps) => {
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
    console.log("handleChangeRun: " + e.target.checked);
    const run = !!e.target.checked;
    changeRunCallback(run);
  }

  return (
    <div>
      <TapeLoadModal
	modalIsOpen={modalIsOpen}
	closeModal={closeModal} loadTape={loadTape} />
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
}

type LoadTapeCallback = (bytes: Uint8Array) => void;


function Box(props) {
  return (<Grid.Item
    row={props.row}
    column={props.column}
    style={{ backgroundColor: "lightgray", color: "black", borderRadius: "5px", padding: "20px"}}
  >{props.children}</Grid.Item>
  );
}


export const MainGrid = (props: MainGridProps) => (
  <div>
    <Grid
      gap="10px"
      columns="1fr 9fr"
      rows="auto auto 60%"
    >
      <Box column="1 / span 3" row="1" overflowY="scroll">
<Instructions /></Box>
      <Box column="1 / span 3" row="2">
	<Flex flexDirection="row">
	  <AlarmPanel customStyles={{float: "left"}}
	    alarmStatuses={props.alarmController.all_alarm_info()}
	    maskedChangeCallback={props.alarmController.set_alarm_masked.bind(props.alarmController)}
	    registerStatusCallback={props.alarmController.set_alarm_status_callback.bind(props.alarmController)}
	  />
	  <IoPanel ioController={props.ioController} customStyles={{float: "left"}} />
	</Flex>
      </Box>
      <Box column="1" row="3">
	<Buttons
	  changeRunCallback={props.tx2Controller.changeRun.bind(props.tx2Controller)}
	  tx2Controller={props.tx2Controller}
	  isClockRunning={props.tx2Controller.isClockRunning()}
	  loadTape={props.loadTape}
	/>
      </Box>
      <Box column="2" row="3" padding="20px" overflowY="scroll">
	<LincolnWriter unit={"66"} cursor_blink_ms={750} />
      </Box>
    </Grid>
  </div>
);
