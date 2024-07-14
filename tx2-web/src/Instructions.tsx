import React, { useState } from 'react';
import styles from './styles.scss';

export function Instructions(): JSX.Element {
  const [instructionsVisible, setInstructionsVisible] = useState(true);

  function toggleInstructionsVisibility() {
    setInstructionsVisible(!instructionsVisible);
  }

  return (
    <section className={styles['instructions']}>
      <button onClick={toggleInstructionsVisibility}>
        {instructionsVisible ? 'Hide Instructions' : 'Show Instructions'}
      </button>
      {instructionsVisible && (
        <>
          <p>Here are some getting-started instructions.</p>
          <ol>
            <li> Press &quot;Mount Paper Tape&quot; and press the button to load the &lsquo;hello&rsquo; sample file.</li>
            <li> Press the CODABO (TSR) button.</li>
          </ol>
          <p>
            Presently you should see some output.
            You can <a href="https://tx-2.github.io/">find out more about
            the simulator project on our website</a> or <a
              href="https://github.com/TX-2/TX-2-simulator">take a
              look at the source code</a>.
          </p>
        </>
      )}
    </section>
  );
}
