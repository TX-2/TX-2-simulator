# Debugging the Command-Line Based Tools and Emulator

If you want to see more detail on what is happening, you can get it by
setting the `RUST_LOG` environment variable.

For example, to use this to see more-detailed information about what
 is happening inside the CLI-based emulator, you might do this:

```
RUST_LOG=debug cargo run --bin cli -- examples/hello.tape
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
