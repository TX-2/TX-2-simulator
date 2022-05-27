import React, { useState, FunctionComponent } from 'react';
import ReactDOM from 'react-dom';
import Modal from 'react-modal';
import Checkbox from './checkbox';
import styled from 'styled-components';

import { codabo, load_tape, start_clock, stop_clock, is_clock_running } from './model/machine'

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

const Buttons: FunctionComponent = () => {
    let subtitle;
    const [ modalIsOpen, setIsOpen ] = React.useState(false);
    const [ isRunning, setIsRunning ] = React.useState(false);

    function openModal() {
	setIsOpen(true);
    }
    function closeModal() {
	setIsOpen(false);
    }
    const customStyles = {
	content: {
	    top: '50%',
	    left: '50%',
	    right: 'auto',
	    bottom: 'auto',
	    marginRight: '-50%',
	    transform: 'translate(-50%, -50%)',
	},
    };

    const TapeLoadModal: FunctionComponent = () => {

	const handleChange = (e: React.ChangeEvent<HTMLInputElement>) => {
	    const file: File = e.target.files![0];
	    console.log("Attempting to load a tape " + file.name + " which has length " + file.size);
	    let reader = new FileReader();
	    reader.onloadend = function () {
		var bytes = new Uint8Array(reader.result as ArrayBuffer)
		load_tape(bytes);
		closeModal();
	    };
	    reader.readAsArrayBuffer(file);
	}

	return <Modal
	isOpen={modalIsOpen}
	onRequestClose={closeModal}
	style={customStyles}
	contentLabel="Load Paper Tape"
	    >
	    <h2 ref={(_subtitle) => (subtitle = _subtitle)}>Load Paper Tape Image</h2>
            <div>
	    <p>Please select a paper tape image file to load. If you do not already have one, you can assemble a program to generate a tape image. </p>
	    <p> An example tape image, <code>hello.tape</code>, is also included in the git repository for the simulator. <a href="https://github.com/TX-2/TX-2-simulator/raw/main/examples/hello.tape">Download it here</a>.</p>
	    <p>After you have chosen the tape file, start the
	computer by pressing the CODABO button.</p>
	    </div>
	    <form>
            <label>Load a tape image file:&nbsp;
            <input type="file" id="tape_load_file" accept=".tape,application/binary"
	onChange={handleChange} />
	</label>
	    </form>
	    </Modal>;
    };

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
	<TapeLoadModal />
	<button id="codaboTSRBtn" onClick={codabo}>CODABO (TSR)</button>
	<button id="tapeLoadBtn" onClick={openModal}>Mount Paper Tape</button>
	<Checkbox label="Run" handleChange={handleChangeRun} isChecked={is_clock_running()} />
	</ButtonsBox>;
};

const MachineStatus = () => {
    return <MachineStatusBox>Machine status information will
    eventually go here.</MachineStatusBox>;
};

const LincolnWriterBox = styled(Box)`
grid-column: 2 / 2;
grid-row: 2 / 2;

overflow-y: scroll;
padding: 20px;
`;

const Paper = styled.div`
border: 1px;
border-color: black;
border-style: solid;

margin-top: 0px;
margin-bottom: 0px;
margin-right: 1em;
margin-left: 1em;

font-family: monospace;
background-color: rgb(255, 255, 240);
`;

const Lw66 = () => {
    return <LincolnWriterBox><Paper>This is the LW66 output.</Paper></LincolnWriterBox>;
};

const GridWrapper = styled.div`
display: grid;
grid-gap: 10px;
grid-template-columns: 1fr 9fr;
grid-template-rows: 100px minmax(100px, auto);
background-color: #fff;
color: #444;
width: 90vw;
height: 90vh;
`;

export const MainGrid = () => {
    return <GridWrapper><MachineStatus/><Buttons/><Lw66/></GridWrapper>;
};
