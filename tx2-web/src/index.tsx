import { App } from './App';
import { init } from '../built-files/build/tx2_web';
import Modal from 'react-modal';
import React from "react";
import ReactDOM from "react-dom";
import { Tx2Controller } from './controller/tx2'

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
  alert("Failed to initialise the WASM code; please report this as a bug: " +
    extractMessage(error))
}

function get_log_level(hashval: string) {
  if (hashval == "") {
    return "debug";
  } else {
    return hashval.substring(1);
  }
}


import("../built-files/build/tx2_web")
  .then(_module => { // eslint-disable-line @typescript-eslint/no-unused-vars
    Modal.setAppElement('body')
    init(get_log_level(window.location.hash));
    const tx2: Tx2Controller = new Tx2Controller();
    ReactDOM.render(<App tx2Controller={tx2} />, document.getElementById("root"));
  })
  .catch(handleError);
