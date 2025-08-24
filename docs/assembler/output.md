# Assembler Output Format

The output file is a binary file representing a punched tape.  It
includes the reader leader.  Each byte of the output file contains six
bits of the tape data (in bits 0 to 5).  The data is written in the
splayed format.  That is the format in which the boot code expects to
read the input tape.

You can upload these tape files into the simulator to run them.
