import React, { FunctionComponent, ReactElement } from 'react';
import { Instructions } from './Instructions';
import Checkbox from './checkbox';
import { LincolnWriter } from './LincolnWriter';
import AlarmPanel, { AlarmControlProps } from './AlarmPanel';
import TapeLoadModal from './TapeLoadModal';
import styled from 'styled-components';
import { Tx2Controller } from 'controller/tx2';
import { AlarmController } from 'controller/alarms';

const Box = styled.div`
background-color: lightgray;
color: black;
border-radius: 5px;
padding: 20px;
/* font-size: 150%; */
`;

const ButtonsBox = styled(Box)`
grid-column: 1 / 2;
grid-row: 2 / 2;
`;

const MachineStatusBox = styled(Box)`
grid-column: 1 / span 2;
grid-row: 1 / 1;
`;

interface ButtonsProps {
  changeRunCallback(run: boolean): void,
  tx2Controller: Tx2Controller,
  isClockRunning: boolean,
  loadTape: (Uint8Array) => void,
}

const Buttons = ({changeRunCallback, tx2Controller, isClockRunning, loadTape}: ButtonsProps) => {
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


  return <ButtonsBox>
    <TapeLoadModal
      modalIsOpen={modalIsOpen}
      closeModal={closeModal} loadTape={loadTape} />
    <button id="codaboTSRBtn"
      onClick={tx2Controller.codabo.bind(tx2Controller)}>CODABO (TSR)</button>
    <button id="tapeLoadBtn" onClick={openModal}>Mount Paper Tape</button>
    <Checkbox label="Run" handleChange={handleChangeRun.bind(this)} isChecked={isRunning} />
	</ButtonsBox>;
};

const MachineStatus = () => {
	return <MachineStatusBox><Instructions />Machine status information will
		eventually go here.</MachineStatusBox>;
};

const LincolnWriterBox = styled(Box)`
grid-column: 2 / 2;
grid-row: 2 / 2;

overflow-y: scroll;
padding: 20px;
`;

const Lw66 = () => {
	return <LincolnWriterBox><LincolnWriter unit={"66"} cursor_blink_ms={750} /></LincolnWriterBox>;
};

const GridWrapper = styled.div`
display: grid;
grid-gap: 10px;
grid-template-columns: 1fr 9fr;
grid-template-rows: 1fr 9fr;
background-color: #fff;
color: #444;
width: 90vw;
height: 90vh;
`;

interface MainGridProps {
  tx2Controller: Tx2Controller,
  alarmController: AlarmController,
  loadTape: (bytes: Uint8Array) => void,
}

type LoadTapeCallback = (bytes: Uint8Array) => void;


export const MainGrid = (props: MainGridProps) => (
  <div>
    <GridWrapper>
      <MachineStatus />
      <Buttons
	changeRunCallback={props.tx2Controller.changeRun.bind(props.tx2Controller)}
	tx2Controller={props.tx2Controller}
	isClockRunning={props.tx2Controller.isClockRunning()}
	loadTape={props.loadTape}
      />
      <Lw66 />
    </GridWrapper>
    <AlarmPanel
      alarmStatuses={props.alarmController.all_alarm_info()}
      maskedChangeCallback={props.alarmController.set_alarm_masked.bind(props.alarmController)}
      registerStatusCallback={props.alarmController.set_alarm_status_callback.bind(props.alarmController)}
    />
  </div>
);
