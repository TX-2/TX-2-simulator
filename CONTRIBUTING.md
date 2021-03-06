# TX-2 Contributor's Guide

First of all, thank you for contributing to the TX-2 project.

We hope to celebrate MIT Lincoln Lab's historic TX-2 computer and some
of the pioneeting software created for it by re-creating the computer
in the form of a simulator and making it possible to run that software
again.

This guide explains what kinds of contribution we're looking for and
explains how you can help.

## What Contributions are Needed?

We need:

* TX-2 Software
* Additional documentation
* Programming contributions to implement missing features

We're hoping that we can get some of these things from [MIT Lincoln
Lab](https://www.ll.mit.edu/) and from the people who worked on the
TX-2.

### TX-2 Software

Our greatest need is for TX-2 software, either in printed/scanned for
or (even better) machine-readable form.

We know that Lincoln Lab holds no machine-readable software for the
TX-2.

Our most pressing need is for a copy of the Sketchpad code (binary or
source).  We have a scanned copy of the Sketchpad code from the
Computer History Museum (donated to them by Ivan Sutherland), but this
is illegible in places.  If you have or know someone who might have a
copy of this, please reach out to us.

### Documentation

While we have some documentation already, it will help to have more.
Please see our [documentation
page](https://tx-2.github.io/documentation.html) for a list of the
documentation we already have.   If you know of documentation not
already in that list, please let us know.

### Safeguarding of Materials

We understand that some of these materials are unique and
irreplaceable.  You don't need to send them to us.  We could, for
example, ask some professional computing historians to help and/or ask
the [Computer History Museum](https://computerhistory.org/) to assist
(they've been very helpful in the past).  If you prefer to simply send
us an electronic version of the document you have, that works for us.

### Contributing by Programming

We also need help in implementing the instructions and machine
features we already have documentation for.  Some important things
that still need to be written are recorded in the [issues
list](https://github.com/TX-2/TX-2-simulator/issues).  Items which we
think are good choices for fist-time contributors are [marked with the
"good first issue"
tag](https://github.com/TX-2/TX-2-simulator/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22).

The "good first issue" tags are marked that way mainly because they
implement a simple instruction and there is something in the existing
code to guide you.

If you are planning a significant contribution which doesn't already
have an issue, please create one and outline what you hope to do.

If you are unfamiliar with Github, or Git or Rust, please let us know
so that we can help you to get started.

## Guidelines for Code Contributions

- [ ] Contributions must use the [MIT
      license](https://github.com/TX-2/TX-2-simulator/blob/main/LICENSE-MIT).
- [ ] Please keep pull requests small, even if this means you don't
      fully implement the feature you have in mind in the first pull
      request.
- [ ] When making code changes, please include in comments a reference
      to the part of the documentation relevant to the code you're
      writing.  For example, when you implement an opcode or hardware
      device, please include a reference to the documentation which
      describes it.
- [ ] Please include tests.

## Say Hello

If you're considering becoming a contributor or have questions, please
let me know by email how I can help you.  Send email to
james@youngman.org.
