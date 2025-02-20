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

The assembler isn't finished yet, so there are a number of quite
severe limitations:

* No support for deferred operands or RC ("Register-Containing") words.
* No support for macros.  Confusingly, the TX-2 assembler supported
  macros and was called M4, but is unrelated to the Unix program `m4`.

## Documentation

The original M4 assembler was documented in chapter 6 of the [TX-2
Users
Handbook](https://tx-2.github.io/documentation#tx-2-users-handbook).
