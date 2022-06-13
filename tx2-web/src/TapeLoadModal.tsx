import React, { FunctionComponent } from 'react';
import Modal from 'react-modal';

interface TapeLoadModalProps {
  modalIsOpen: boolean;
  closeModal: () => void;
  loadTape: (bytes: Uint8Array) => void;
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

const TapeLoadModal: FunctionComponent<TapeLoadModalProps> = ({modalIsOpen, closeModal, loadTape}) => {

        const handleChange = (e: React.ChangeEvent<HTMLInputElement>) => {
                const file: File = e.target.files![0];
                console.log("Attempting to load a tape " + file.name + " which has length " + file.size);
                const reader = new FileReader();
                reader.onloadend = function() {
                        const bytes = new Uint8Array(reader.result as ArrayBuffer)
                        loadTape(bytes);
                        closeModal();
                };
                reader.readAsArrayBuffer(file);
        }

        return <Modal
                isOpen={modalIsOpen}
                onRequestClose={closeModal}
                style={customStyles}
                contentLabel="Load Paper Tape"
        ><h2>Load Paper Tape Image</h2>
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
export default TapeLoadModal;
