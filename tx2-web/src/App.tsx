import React, { useState, useRef } from "react";

import { Instructions } from './Instructions';
import { MainGrid } from './MainGrid';
import { create_tx2 } from './machine'

type AppState = {
    running: boolean;
    sleep_multiplier: number;
};

//let next_tick: number  = m.tx2_next_simulated_tick(machine);
//console.log("Next TX-2 tick at " + next_tick);

export class App extends React.Component {
   // systemTime is not in state because we don't want an app UI
    // refresh on every timer tick.
    state: AppState;

    constructor(props) {
	super(props);

	create_tx2();

	this.state = {
	    running: false,
	    sleep_multiplier: 1.0,
	};
    }

    render() {
	return <div><Instructions /><MainGrid /></div>;
    }
}
