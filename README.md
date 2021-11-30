# TX-2-Instruction-Simulator

From https://en.wikipedia.org/wiki/TX-2:

The MIT Lincoln Laboratory TX-2 computer was the successor to the
Lincoln TX-0 and was known for its role in advancing both artificial
intelligence and human–computer interaction. Wesley A. Clark was the
chief architect of the TX-2.

## To Build The Code

To be able to build the code, [install the Rust build
tools](https://doc.rust-lang.org/cargo/getting-started/installation.html).

## Trying It Out

The current simulator is not yet advanced enough to be interactive.
To try it out, simply run

```
cargo run
```

This will build the code (if necessary) and then run it.


### Getting More Detail on the Internals

Right now the simulator doesn't have enough I/O support to be usable
interactively, and only implements enough instructions to get part-way
through the boot process.  So there is not much to see, yet.

If you do want to see more detail, you can get it by setting the
`RUST_LOG` environment variable when you run the code:

```
RUST_LOG=debug cargo run
```

For even more detail:

```
RUST_LOG=trace cargo run
```

Full details on how to configure the logging output are in the
[documentation for the tracing-subscriber
crate](https://docs.rs/tracing-subscriber/0.2.25/tracing_subscriber/filter/struct.EnvFilter.html),
though the [analogous docmenation for
env_logger](https://docs.rs/env_logger/0.7.1/env_logger/#enabling-logging)
is probably more accessible.
