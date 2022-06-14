import React from 'react';
import styles from './styles.scss'

export function Instructions(): JSX.Element {
  return (<section className={styles['instructions']}>
    <p>Here are some getting-started instructions.</p>
    <ol>
      <li> Press &quot;Mount Paper Tape&quot; and select the <code>hello.tape</code> file.</li>
      <li> Press the CODABO (TSR) button</li>
      <li> Check the &quot;Run&quot; checkbox.</li>
    </ol>
    <p>
      Presently you should see some output.
      You can <a href="https://tx-2.github.io/">find out more about
        the simulator project on our website</a> or <a
        href="https://github.com/TX-2/TX-2-simulator">take a
        look at the source code</a>.
    </p>
  </section>);
}
