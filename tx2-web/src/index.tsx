import React from "react";
import ReactDOM from "react-dom";
import { set_app_wasm_mod } from './model/machine'
import Modal from 'react-modal';
import { Tx2Controller } from './controller/tx2'

import { App } from './App';

const wasm = import("../build/tx2_web");

function showErrorAlert(message: string) {
  alert("Failed to initialise the WASM code; please report this as a bug: " + message);
}

const has = <K extends string>(
  key: K,
  x: object,
): x is { [key in K]: unknown } => (
  key in x
);

function extractMessage(error: unknown): string {
  let message = 'Unknown error';
  if (!error) {
    /* use the default message we already chose. */
  } else if (typeof error == 'string') {
    message = error;
  } else if ((typeof error == 'object') && has('message', error) && (typeof error.message == 'string')) {
    message = error.message;
  }
  return message;
}

function handleError(error: unknown) {
  showErrorAlert(extractMessage(error))
}

wasm
  .then(m => {
    Modal.setAppElement('body')
    m.init();
    set_app_wasm_mod(m);
    const tx2: Tx2Controller = new Tx2Controller();
    ReactDOM.render(<App tx2Controller={tx2} />, document.getElementById("root"));
  })
  .catch(handleError);
