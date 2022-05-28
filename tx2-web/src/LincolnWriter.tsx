import React, { Component } from 'react';
import styled from 'styled-components';

const Paper = styled.div`
border: 1px;
border-color: black;
border-style: solid;

margin-top: 0px;
margin-bottom: 0px;
margin-right: 1em;
margin-left: 1em;

padding-left: 0.5ex;
padding-right: 0.5ex;

font-family: monospace;
background-color: rgb(255, 255, 240);
`;

const ComputerOutput = styled.span`
border: 0px;
border-style: none;
margin: 0px 0px;
font-family: monospace;
`;

const OpaqueCursor = styled(ComputerOutput)`
  opacity: 1.0;
`;
const TransparentCursor = styled(ComputerOutput)`
  opacity: 0.0;
`;

type CursorState = {
  isSolid: boolean;
};
type CursorProps = {
  blinkMs: number,
};

class Cursor extends Component<CursorProps, CursorState> {
  private intervalId: NodeJS.Timeout | undefined;
  constructor(props: CursorProps) {
    super(props);
    this.state = {
      isSolid: true,
    }
  }
  componentDidMount() {
    this.intervalId = setInterval(
      () => {
	this.setState(prevState => {
	  return {
	    isSolid: !prevState.isSolid,
	  };
	});
      }, this.props.blinkMs);
  }
  componentWillUnmount() {
    clearInterval(this.intervalId);
  }
  render() {
    if (this.state.isSolid) {
      return <OpaqueCursor>&#9608;</OpaqueCursor>;
    } else {
      return <TransparentCursor>&#9608;</TransparentCursor>;
    }
  }
}

type LincolnWriterProps = {
  cursor_blink_ms: number,
  unit: string,
};
export class LincolnWriter extends React.Component<LincolnWriterProps, {}> {
  prefix: string = "lw" + this.props.unit;
  historyId = this.prefix + "-history";
  currentId = this.prefix + "-current-line";

  render() {
    return <Paper>
      <ComputerOutput id={this.historyId}></ComputerOutput>
      <ComputerOutput id={this.currentId}></ComputerOutput>
      <Cursor blinkMs={this.props.cursor_blink_ms} />
    </Paper>;
  }
}
