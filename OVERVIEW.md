# Design Overview

This document provides an overview of the design of the simulator.
For a more general introduction, see [README.md](README.md).

## Current State

We're in the early stages of implementation.  Most opcodes and most
hardware are not implemented yet.  We have enough implemented opcodes
and hardware that the boot code works and the machien tries to load a
binary from paper tape, in the normal boot process.  But so far that's
it.

This is going to mean that our design will change as implementation
proceeds.  The purpose of this document, then, is to explain the
design enough so that contributors can find their way around and begin
to contribute changes.

Some people's contributions will necessarily change the design, and
that's welcome.

## Components

The major components of the design are split into separate Rust
crates.  In Rust, the crate is the basic unit of compilation; Rust
builds crates as a unit.  There is a finer granularity; the crates are
divided into modules.

The crates are listed in the [top-level manifest file](Cargo.toml);
they are:

### base

The base crate implements

* Signed one's complement types for the TX-2 machine word
* Signed one's complement types for sub-words
* Unsigned types for TX-2 words and sub-words
* Special-purpose signed or unsigned types used by the TX-2 (as filds
  in the instruction for example).
* A representation of the machine instruction suitable for use in the
  simulator or an assembler.
* character-set conversion utilities

We keep these aspects of the implementation in a separate crate so
that the assembler doesn't have to depend on the simulator itself.

### cpu

The simulator itself, implemented as a library.  This implements the
CPU instructions, the system's memory and its I/O devices.

The simulator library is reactive; you call it repeatedly to make it
do things like execute instructions or simulate I/O operations.

In principle the simulator library should be non-blocking but right
now it does perform blocking I/O for reads of the simulated paper
tape.

### cli

This is a basic command-line interface to the simulator.  It boots the
machine.  The built-in boot code attempts to load and run a binary
from the paper tape drive (the tape data is provided via a file named
on the command line, see the `--help` output).

This part of the design likely won't last very long, because it won't
support devices like the light pen or CRT without significant change.
But it should allow us to test and debug the loading of programs.

### assembler

This is a command-line assembler which will eventually read Unicode
input files and generate data files suitable to be loaded as simulated
paper tapes.

The syntax of the assembler input is intended to follow that of the
standard TX-2 assembler which was called M4.

The reason for using Unicode as input is so that the input file can,
as far as possible, look like the normal representation of M4 source
code.  At some point we may also define a pure-ASCII equivalent (so
that something like `\\doublehand` would be understood to be a synonym
for `☛☛`.   But nothing like this is implemented right now.

## Future Directions

Clearly, we hope to implement more of the missing features
(e.g. remaining opcodes and hardware devices).  We'd like to end up
with a working WASM-based simulator which people can try out over the
web.  We're inspired by the example of
Matt Godbolt's [jsbeeb](https://bbc.godbolt.org/).

## Other Sources of Information

The code is extensively commented, but you may also find it helpful to
read some of our [reference
documentation](https://tx-2.github.io/documentation.html).
