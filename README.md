# TX-2 Simulator

We are trying to create a simulator for Lincoln Lab's historic TX-2
computer.  Notably, this is the computer on which Ivan Sutherland's
Sketchpad program ran.

From [the Wikipedia entry for the TX-2](https://en.wikipedia.org/wiki/TX-2):

> The MIT Lincoln Laboratory TX-2 computer was the successor to the
> Lincoln TX-0 and was known for its role in advancing both artificial
> intelligence and human–computer interaction. Wesley A. Clark was the
> chief architect of the TX-2.

## To Build The Code

To be able to build the code, [install the Rust build
tools](https://doc.rust-lang.org/cargo/getting-started/installation.html).

## Trying It Out

The current simulator is not yet advanced enough to be interactive.
To try it out, simply run

```
cargo run --bin cli
```

This will build the code (if necessary) and then run it.


### Getting More Detail on the Internals

Right now the simulator doesn't have enough I/O support to be usable
interactively, and only implements enough instructions to get part-way
through the boot process.  So there is not much to see, yet.

If you do want to see more detail, you can get it by setting the
`RUST_LOG` environment variable when you run the code:

```
RUST_LOG=debug cargo run --bin cli
```

For even more detail:

```
RUST_LOG=trace cargo run --bin cli
```

Full details on how to configure the logging output are in the
[documentation for the tracing-subscriber
crate](https://docs.rs/tracing-subscriber/0.2.25/tracing_subscriber/filter/struct.EnvFilter.html),
though the [analogous docmenation for
env_logger](https://docs.rs/env_logger/0.7.1/env_logger/#enabling-logging)
is probably more accessible.

## Contributing

If you are considering contributing, first of all, thanks!

We have quite a lot of [documentation about the operation and
programming of the TX-2](https://tx-2.github.io/documentation.html).
This is what our implementation is based on.

Please see our [Contributor's Guide](CONTRIBUTING.md) for information
on what we need and how you can help.  The Guide also explains what
non-coding contributions are needed and how to identify a good "first
issue" to pick up.
