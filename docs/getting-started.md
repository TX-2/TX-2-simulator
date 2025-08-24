# Getting Started

This project has several components:

- Command-line tools for assembling, disassembling and inspecting TX-2
  programs
- A TX-2 emulator which runs locally in your web browser
- A more limited command-line emulator

## Build Tools

The TX-2 emulator and its associcated tools are written in Rust.  The
browser-based emulator is partially written in TypeScript.

### Rust

To be able to build the Rust code, [install the Rust build
tools](https://doc.rust-lang.org/cargo/getting-started/installation.html).

### Browser-based Components

The web-based simulator runs locally in a browser.   It is implemented
as a WASM program (we compile the Rust simulator code to WASM), some
Javascript glue, and an HTML page which acts as a container.

There is no server-side component to the simulator, except that it's
convenient to download the HTML, the WASM and the Javascript from a
web server.  The simulator doesn't execute on the server.

#### Installing the WASM Toolchain

1. Follow the instructions above to install the Rust
   toolchain.
1. Install wasm-pack with `cargo install wasm-pack`.
1. [Install npm](https://docs.npmjs.com/getting-started).
1. If you already have `npm` installed, make sure it is up-to-date by
   running `npm install npm@latest -g`

You should not need `cargo-generate`.

If these instructions seem not to work and the tips in [Build
Trouble](build-trouble.md) don't help, then please [raise a
bug](https://github.com/TX-2/TX-2-simulator/issues/new/choose).


## Building the Code

While it is possible to build just the CLI components (the CLI-based
emulator, assembler and associated tools), these instructions assume
you want to build everything.

### Build the CLI Tools

```sh
cargo buld --workspace
```

### Build the Browser-based Emulator

```sh
cd tx2-web
npm run build
```

## Running the Emulator

To run the browser-based emulator:

```sh
cd tx2-web
npm run dev
```

The CLI-based emulator is more limited (some I/O devices are not
implemented in the CLI emulator).  You can run it like this:

```
cargo run --bin cli -- examples/hello.tape
```

See [Debugging Tips](debugging) for tips on how to troubleshoot and
debug the emulator.

## Using the Assembler

If you want to do more than try out the provided example programs, you
will need to use the assembler. See [Getting Started with the
Assembler](assembler/getting-started.md) for information on how to do
this.
