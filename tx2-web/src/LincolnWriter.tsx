import Keyboard from './Keyboard'
import React from 'react';
import styles from './styles.scss'

type LincolnWriterProps = {
  unit: string,
};
type LincolnWriterState = Record<string, never>;

export class LincolnWriter extends React.Component<LincolnWriterProps, LincolnWriterState> {
  prefix: string = "lw" + this.props.unit;
  historyId = this.prefix + "-history";
  currentId = this.prefix + "-current-line";
  keyboardId = this.prefix + "-keyboard"

  render(): React.ReactElement {
    return (<div className={styles['lw']}>
      <div className={styles['lw__output']}>
        <div className={styles['lw__paper']}>
          <span className={styles['lw__output']} id={this.historyId}></span>
          <span  className={styles['lw__output']} id={this.currentId}></span>
          <span className={styles['lw__cursor']}>&nbsp;</span>
        </div>
      </div>
      <Keyboard className={styles['lw__input__keyboard']} hdClass={styles['lw__input__keyboard_hits']} />
    </div>);
  }
}
