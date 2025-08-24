# Limitations

The assembler is incomplete and changes quite often.  It has a lot of
limitations right now.

## Unimplemented Features

Some features are not yet supported, or are supported only a limited
way:

- [Macro expansion is only partially supported](https://github.com/TX-2/TX-2-simulator/issues/120)
- [Compound characters](compound-characters.md) are not supported.
- The `T` command should control the interpretation of the tab
  character, but this is not yet supported.
- The ☛☛RC command is not implemented. It's not clear that
  implementing it would be useful.

## Redundant Commands

The TX-2 M4 asembler provided some metacommands which aren't useful on
modern computers having general-purpose text-editing facilities.  The
☛☛XXX, ☛☛INSERT, ☛☛DELETE and ☛☛REPLACE editing commands aren't needed
or implemented.

Similarly, the metacommands ☛☛TYPE, ☛☛LIST, ☛☛DIR, ☛☛LDIR, ☛☛TDIR, and
☛☛PLIST are not implemented.  Instead pass the flag `--list` to the
assembler to obtain a listing.

The functions of the ☛☛LW, ☛☛READ and ☛☛SAVE metacommands are provided
by the assembler command-line.  The ☛☛RECONVERT metacommand isn't
described in any detail in the User Handbook document, but it also
probably isn't needed.

## Memory I/O

The ☛☛CORE and ☛☛TAPE commands are probably better implemented somehow
in the simulator than in the assembler.  Similarly for ☛☛GOTO.

The ☛☛BIN and ☛☛CLEAN commands probably aren't needed and so are not
implemented.

## Undocumented Commands

The Users Handbook mentions the ☛☛DEMO metacommand but doesn't explain
what it does, so this is not implemented.

## TX-2 Project Issues

See the [TX-2 Simulator project's
issues](https://github.com/TX-2/TX-2-simulator/issues) for a full list
of the limitations of both the assembler and the TX-2 emulator.

## Documentation

The original M4 assembler was documented in chapter 6 of the [TX-2
Users
Handbook](https://tx-2.github.io/documentation#tx-2-users-handbook).
