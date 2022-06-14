import { MainGrid } from './MainGrid';
import React from "react";
import { Tx2Controller } from './controller/tx2';

interface AppProps {
  tx2Controller: Tx2Controller,
}

export class App extends React.Component<AppProps> {
  constructor(props: AppProps) {
    super(props);
  }

  render(): React.ReactElement {
    return <div>
      <MainGrid
        tx2Controller={this.props.tx2Controller}
        alarmController={this.props.tx2Controller.alarmController}
        ioController={this.props.tx2Controller.ioController}
        loadTape={this.props.tx2Controller.loadTape.bind(this.props.tx2Controller)}
      />
    </div>;
  }
}
