import React from "react";
import { MainGrid } from './MainGrid';
import { create_tx2 } from './model/machine'

export class App extends React.Component {
	constructor(props) {
		super(props);
		create_tx2();
	}

	render(): React.ReactElement {
		return <div><MainGrid /></div>;
	}
}
