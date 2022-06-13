import React, { Component } from 'react';
import styled from 'styled-components';
import styles from './styles.scss'

//function Box(props: GridItemProps) {

function Paper(props: any) {
  return <div className={styles['lw__paper']}>{props.children}</div>;
}

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
  opacity: 0.2;
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
  render(): React.ReactElement {
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

  render(): React.ReactElement {
    return <Paper>
      <ComputerOutput id={this.historyId}></ComputerOutput>
      <ComputerOutput id={this.currentId}></ComputerOutput>
      <Cursor blinkMs={this.props.cursor_blink_ms} />
    </Paper>;
  }
}
