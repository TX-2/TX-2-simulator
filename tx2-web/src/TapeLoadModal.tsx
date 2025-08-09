import React, { FunctionComponent } from 'react';
import Modal from 'react-modal';
import styles from './styles.scss'

interface TapeLoadModalProps {
  modalIsOpen: boolean;
  closeModal: () => void;
  loadTape: (bytes: Uint8Array) => void;
  loadSample: (name: string) => void;
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
  overlay: {zIndex: 1000},
};

const TapeLoadModal: FunctionComponent<TapeLoadModalProps> = ({ modalIsOpen, closeModal, loadTape, loadSample }) => {
  const handleLoadEcho = (e: React.MouseEvent<HTMLInputElement>) => {
    console.log({ e });
    loadSample("echo");
    closeModal();
  }
  const handleLoadHello = (e: React.MouseEvent<HTMLInputElement>) => {
    console.log({ e });
    loadSample("hello");
    closeModal();
  }
  const handleChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    const files = e.target.files;
    if (files) {
      const file: File = files[0];
      console.log("Attempting to load a tape " + file.name + " which has length " + file.size.toString(10) + " (decimal)");
      const reader = new FileReader();
      reader.onloadend = function() {
        const bytes = new Uint8Array(reader.result as ArrayBuffer)
        loadTape(bytes);
        closeModal();
      };
      reader.readAsArrayBuffer(file);
    } else {
      console.log("TapeLoadModal.handleChange: change target has unset files");
    }
  }

  return <Modal
    isOpen={modalIsOpen}
    onRequestClose={closeModal}
    style={customStyles}
    contentLabel="Load Paper Tape"
  ><h2>Load Paper Tape Image</h2>
    <div><p>Please select a paper tape image file to load.</p>
      <p>You can press one of the buttons which load a canned example,
        or use the &quot;Choose file&quot; button to upload your own program and run it.</p></div>
    <form>
      <div className={styles['tape-load-modal__buttons']}>
        <input className={styles['tape-load-modal__buttons']} type="button" onClick={handleLoadHello} value="Load sample &lsquo;hello&rsquo;" />
        <input className={styles['tape-load-modal__buttons']} type="button" onClick={handleLoadEcho} value="Load sample &lsquo;echo&rsquo;" />
        <input className={styles['tape-load-modal__buttons']} type="file" id="tape_load_file" accept=".tape,application/binary" onChange={handleChange} />
      </div>
    </form>
  </Modal>;
};
export default TapeLoadModal;
