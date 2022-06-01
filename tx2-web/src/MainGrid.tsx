import React, { FunctionComponent, ReactElement } from 'react';
import { Instructions } from './Instructions';
import Checkbox from './checkbox';
import { LincolnWriter } from './LincolnWriter';
import AlarmPanel, { AlarmControlProps } from './AlarmPanel';
import TapeLoadModal from './TapeLoadModal';
import styled from 'styled-components';

import { all_alarm_info, codabo, start_clock, stop_clock, is_clock_running, AlarmStatus } from './model/machine'

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

const Buttons: FunctionComponent = (): ReactElement => {
	const [modalIsOpen, setIsOpen] = React.useState(false);
	const [isRunning, setIsRunning] = React.useState(false);

	function openModal() {
		setIsOpen(true);
	}
	function closeModal() {
		setIsOpen(false);
	}
	function handleChangeRun(e: React.ChangeEvent<HTMLInputElement>) {
		console.log("handleChangeRun: " + e.target.checked);
		if (e.target.checked) {
			setIsRunning(true);
			start_clock();
		} else {
			setIsRunning(false);
			stop_clock();
		}
	}


	return <ButtonsBox>
		<TapeLoadModal
			modalIsOpen={modalIsOpen}
			closeModal={closeModal} />
		<button id="codaboTSRBtn" onClick={codabo}>CODABO (TSR)</button>
		<button id="tapeLoadBtn" onClick={openModal}>Mount Paper Tape</button>
		<Checkbox label="Run" handleChange={handleChangeRun} isChecked={is_clock_running()} />
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

function convert_alarm_status_to_alarm_control_props(info: AlarmStatus): AlarmControlProps {
  return {
    name: info.name,
    maskable: info.maskable,
    masked: info.masked,
    active: info.active,
    message: info.message
  };
}

export const MainGrid = () => {
  let info = all_alarm_info()
  .map(convert_alarm_status_to_alarm_control_props);
  return (
    <div>
      <GridWrapper><MachineStatus /><Buttons /><Lw66 /></GridWrapper>
      <AlarmPanel info={info}/>
    </div>
  );
};
