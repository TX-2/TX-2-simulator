# TX-2 Simulator

We are trying to create a simulator for Lincoln Lab's historic TX-2
computer. Notably, this is the computer on which Ivan Sutherland's
Sketchpad program ran. If we can get the simulator working, we may be
able to run Sketchpad once again.

From [the Wikipedia entry for the TX-2](https://en.wikipedia.org/wiki/TX-2):

> The MIT Lincoln Laboratory TX-2 computer was the successor to the
> Lincoln TX-0 and was known for its role in advancing both artificial
> intelligence and human–computer interaction. Wesley A. Clark was the
> chief architect of the TX-2.

## For More Information

The [OVERVIEW](docs/OVERVIEW.md) file explains the high-level design
of the simulator. More information is available at the [TX-2
Project's website](https://tx-2.github.io/).

## Trying It Out

The simulator doesn't emulate all the features of the original TX-2
yet, but you can still try it out.

### Try It Out Online

You can try it on-line [here](https://tx-2.github.io/demo/).

### Building and Running the Web-based simulator

To run the web-based version locally yourself, follow [these
instructions](docs/build/web.md).

### Building and Running The Command-Line Tools

Hardware emulation is much less complete in the command-line version.

You can [try out the command-line simulator and tools by following
these instructions](docs/build/cli.md).

## Contributing

If you are considering contributing, first of all, thanks!

We have quite a lot of [documentation about the operation and
programming of the TX-2](https://tx-2.github.io/documentation.html).
This is what our implementation is based on.

Please see our [Contributor's Guide](CONTRIBUTING.md) for information
on what we need and how you can help. The Guide also explains what
non-coding contributions are needed and how to identify a good "first
issue" to pick up.
