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

## Contributing

If you are considering contributing, first of all, thanks!

We have quite a lot of [documentation about the operation and
programming of the TX-2](https://tx-2.github.io/documentation.html).
This is what our implementation is based on.

Our [TX-2 project issues
list](https://github.com/TX-2/TX-2-simulator/issues) includes feature
requests for the things we need to implement next.  Some of these are
labeled as [good first
issue](https://github.com/TX-2/TX-2-simulator/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22)
items, mainly because they implement a simple instruction and there is
something in the existing code to guide you.

If you are keen to contribute but not able or not inclined to use
Github or Rust, email me at james@youngman.org so that we can discuss
how you might be able to help.

Contributions must use the [MIT
license](https://github.com/TX-2/TX-2-simulator/blob/main/LICENSE-MIT).
Please keep pull requests small, even if this means you don't fully
implement the feature you have in mind in the first pull request.
