import React from "react";
import ReactDOM from "react-dom";
import { set_app_wasm_mod } from './model/machine'
import Modal from 'react-modal';
import { Tx2Controller } from './controller/tx2'

import { App } from './App';

const wasm = import("../build/tx2_web");

wasm.then(m => {
  Modal.setAppElement('body')
  m.init();
  set_app_wasm_mod(m);
  let tx2: Tx2Controller = new Tx2Controller();
  ReactDOM.render(<App tx2Controller={tx2} />, document.getElementById("root"));
});
