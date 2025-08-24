# Getting Started with the Assembler

First you will need to build the assembler.  If you have not already
done that, please see the [general Getting Started
guide](../getting-started.md) for instructions.

## A Simple Example

Here's an example input:

```
100|               0
200| h ²¹IOS₅₂ 30106
     h   STE     100
         0
☛☛PUNCH 200
```

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

## More Examples

There are some other examples in the [assembler's `examples`
folder](../../assembler/examples).  Those examples are the source code
for the tape images in the [top-level examples
folder](../../examples).

## Learning About the TX-2's Assembly Language

The best reference for the TX-2's assembly language is the [TX-2 Users
Handbook](https://tx-2.github.io/documentation#UH) by Alexander
Vanderburgh.  The handbook as a whole is a guide to programming the
TX-2.  It includes an explanation of the TX-2's architecture and
peripherals.  Chapter 6 describes the assembler in particular.
