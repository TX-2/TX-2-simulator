# Getting Started with the Assembler

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

The output goes to the file `ios.tape`.  You can load that into the
TX-2 emulator and run it.

There are some other examples in the `examples` folder.
