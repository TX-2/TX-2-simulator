# TX-2 Assembler

This program reads assembly language programs and produces files which
emulate punched tapes containing the program.

We aim ultimately to support most of the features of the TX-2 system
assembler, "M4".  Since this is a cross-assembler, some features (such
as invoking the assembled program directly) likely will not be
implemented.

The assembler is very basic right now.  However, it can be used to
generate simple test programs.

## Example

Here's an example input:

<pre>
100|               0
200| h ²¹IOS₅₂ 30106
     h   STE     100
         0
☛☛PUNCH 200
</pre>

This program consists of four words:

* 100: a data storage location
* 200: connect the paper tape reader (leaving its status word in register E)
* 201: store the status word at location 100.
* 202: an invalid instruction which (by default) causes the simulator to stop.

If you put the above assembly language program in the file
`ios.tx2as` you can assemble it like this:

```
cargo run --bin  tx2m4as -- --output ios.tape ios.tx2as
```

The output goes to the file `ios.tape`.

There are some other examples in the `examples` folder.

## Limitations

### Unimplemented Features

Some features are not yet supported, or are supported only a limited
way:

* No support for macros; these can currently be defined but cannot be
  used.  Confusingly, the TX-2 assembler supported macros and was
  called M4, but is unrelated to the Unix program `m4`.
* The `T` command should control the interpretation of the tab
  character, but this is not yet supported.
* The ☛☛RC command is not implemented. It's not clear that
  implementing it would be useful.

### Redundant Commands

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

### Memory I/O

The ☛☛CORE and ☛☛TAPE commands are probably better implemented somehow
in the simulator than in the assembler.  Similarly for ☛☛GOTO.

The ☛☛BIN and ☛☛CLEAN commands probably aren't needed and so are not
implemented.

### Undocumented Commands

The Users Handbook mentions the ☛☛DEMO metacommand but doesn't explain
what it does, so this is not implemented.

## Documentation

The original M4 assembler was documented in chapter 6 of the [TX-2
Users
Handbook](https://tx-2.github.io/documentation#tx-2-users-handbook).
