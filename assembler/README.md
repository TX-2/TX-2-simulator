# TX-2 Assembler

This program reads assembly language programs and produces files which
emulate punched tapes containing the program.

We aim ultimately to support most of the features of the TX-2 system
assembler, "M4".  Since this is a cross-assembler, some features (such
as invoking the assembled program directly) likely will not be
implemented.

The assembler is very basic right now. For example, neither opcodes
nor symbols are supported yet.  However, it can be used to generate
basic test programs.

Here's an example input:

<pre>
100| 0
     0
☛☛PUNCH 100
</pre>

This program consists of two words, both zero (they're not valid
instructions).  It will be loaded at memory address 100 octal.  The
program entry point is also 100 octal.

If you put the above assembly language program in the file
`example.tx2as` you can assemble it like this:

```
cargo run --bin  tx2m4as -- --output 100.tape example.tx2as
```

The output goes to the file `100.tape`.
