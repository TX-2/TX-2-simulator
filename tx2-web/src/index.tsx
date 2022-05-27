import React, { useState, useRef } from "react";
import ReactDOM from "react-dom";
import styled from 'styled-components';
import { set_app_wasm_mod } from './machine'
import Modal from 'react-modal';

import { App } from './App';

const wasm = import("../build/tx2_web");

wasm.then(m => {
    Modal.setAppElement('body')
    m.init();
    set_app_wasm_mod(m);
    ReactDOM.render(<App />, document.getElementById("root"));
});
