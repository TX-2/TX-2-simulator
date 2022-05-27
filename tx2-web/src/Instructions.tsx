import React from 'react';
import styled from 'styled-components';

const Wrapper = styled.section`
background-color: rgb(255, 255, 240);
color: black;
`;

export function Instructions () {
    return (
	<Wrapper>
	    <p>
	    Here are some getting-started instructions.
	    </p>
	    <ol>
	    <li> Press "Mount Paper Tape" and select</li>
	    the <code>hello.tape</code> file.
	    <li> Press the CODABO (TSR) button</li>
	    <li> Press the "Sync: Start" button.</li>
	    </ol>
	    <p>
	    Presently you should see some output.
	    </p>
	    <p>
	    You can <a href="https://tx-2.github.io/"> find out more about
	the simulator project on our website</a>
	    or <a href="https://github.com/TX-2/TX-2-simulator">take a
	look at the source code</a>.
	    </p>
	    </Wrapper>
    );
}
