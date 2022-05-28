# Building and Running the Web-based TX-2 Simulator

## Disclaimer

The web-based simulator is still under development, so you may not get
a result which actually does much even if you follow these
instructions.  For the time being the [command-line](cli.md) simulator
is probably more useful.

## Introduction

The web-based simulator runs locally in a browser.   It is implemented
as a WASM program (we compile the Rust simulator code to WASM), some
Javascript glue, and an HTML page which acts as a container.

There is no server-side component to the simulator, except that it's
convenient to download the HTML, the WASM and the Javascript from a
web server.  The simulator doesn't execute on the server.

## Installing the WASM Toolchain

These instructions are based on the [Rust Game-of-Life WASM
book](https://rustwasm.github.io/docs/book/game-of-life/setup.html).
If these instructions seem not to work then please [raise a
bug](https://github.com/TX-2/TX-2-simulator/issues/new/choose) but
meanwhile you might be about to figure out the problem by looking at
the [Rust Game-of-Life WASM
book](https://rustwasm.github.io/docs/book/game-of-life/setup.html)

### Toolchain Installation Steps

1. [Follow these instructions to install the Rust
   toolchain](https://www.rust-lang.org/tools/install).
1. Install wasm-pack by either [following these scary `curl | sh`
   instructions](https://rustwasm.github.io/wasm-pack/installer/) or
   by using `cargo install wasm-pack`.
1. [Install npm](https://docs.npmjs.com/getting-started).
1. If you already have `npm` install, make sure it is up-to-date by
   running `npm install npm@latest -g`

You should not need `cargo-generate`.

### Build Steps

```sh
$ cd tx2-web
$ npm run build
```

### Trying it Out

```sh
$ cd tx2-web
$ npm run dev
```

The `npm` command will print the URL from which the pages are served,
just visit that in your browser.
