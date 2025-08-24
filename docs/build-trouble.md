# Build Trouble

Here are some tips on solving problems you might have building the
code.

## Command-Line Tools

Problems with building the Command-Line tools are most likely to
relate to updates to the Rust tools.

If you have trouble, please make sure you have a recent set of Rust
build tools (by running `rustup update`).

If you have done that and `cargo build --workspace` still does not
work, please [report an issue in the project's bug
tracker](https://github.com/TX-2/TX-2-simulator/issues/new/choose).

## Browser-based Emulator

On my development system there is often incompatibility between the
Rust development tools (as installed by rustup) and various Node.js
tools installed by my operating system's package manager.  This is
often because the tool versions installed by operating system's
package manager are quite old.

Usually the solution to these is to uninstall the operating system's
installed version (of, for example, webpack or binaryen) and use
`npm`'s version of the tool.

### Problems with wasm-opt

Some versions of `wasm-pack` [have a bug in how they locate the
`wasm-opt` binary](https://github.com/rustwasm/wasm-pack/issues/1062);
they can't correctly find a pre-installed binary.  On my system this
gives rise to this error:

```
[INFO]: found wasm-opt at "/usr/bin/wasm-opt"
Error: /usr/bin/bin/wasm-opt binary does not exist
```

One low-tech workaround for this problem is to move any
locally-installed `wasm-opt` binary out of the way, so that
`wasm-pack` uses a downloaded verson.
