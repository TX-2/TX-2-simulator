# Open Questions

## Architecture

1. Are registers N, P, Q, K, F, FA memory-mapped?
2. If a program manually raises the flag for sequence 0, from where
   does sequence 0 begin executing?  (See also the question about the
   TSP and index register 0, below).
3. Was the U-memory ever fitted?
4. If "trap on sequence change" is active and we change to sequence
   41, is the TRAP sequence (42) activated?   If so, what will it see
   in the E register when it begins to run?
5. What sets the CODABO start point registers 03777710-03777717?
6. What constitutes an invalid address for the purposes of the PSAL
   alarm?  For example, the gap between U-memory and V-memory?   Does
   PSAL fire when P points to a location in S-memory but the S-memory
   is disabled on the console?  Similarly for the other memories which
   can be disabled (T, U, V).
7. If I write to a location which is in practice read-only
   (e.g. non-flip-flop V-memory, such as the plugboard or the shaft
   encoder register) does an alarm occur?
8. If I use the MKC instruction to set the meta bit of an arithmetic
   unit register (register A for example), this apparently just sets
   the meta-bit in the M register (User guide page 5-23).  What is the
   practical significance of this?  Is this event detectable by the
   programmer?
9. Are there any writable locations in the V-memory other than
   registers A, B, C, D, E?  What are they, how do they behave?
10. Is the plugboard which configures sequence priorities
    memory-mapped?  If yes, how does it appear?
11. Does indexation occur during the intermedia deferred addressing
    cycles?   What value is used (a value from the index register, or
    the left-hand-side of the word loaded from the deferred location)?
12. Is there any limit to the number of iterations of deferred address
    loads during deferred addressing?  That is, if memory contains
		0: 000  000 400 001
		1: 000  000 400 000
    instruction and I use [0] in an instruction, will the deferred
    adressing operation loop forever between addresses 0 and 1?


## Instructions

1. Was the XEQ instruction implemented?  This appears as a
   hand-written note on the opcode table of my scanned copy of the
   User handbook, apparently as opcode 2.  But the document doesn't
   describe that instruction.  Sketchpad does not appear to use it.

## Start-Up

1. Does it matter what the N register holds at start-up (e.g. after
   CODABO has been pressed)?  It presumably won't matter if the hold
   bit is set or not, since the active sequence is 0.
2. The manual states that "flip-flops" are reset by CODABO.  Does this
   include zeroing all the flip-flops in V memory?  Does this include
   registers N, P, Q, K, F, FA?
3. Does the "regular" CODABO operation load the value of the TSP
   toggle into index register 0?  Generally what is the relationship
   between the actual program counter used for sequence 0, the TSP and
   index register zero?  (Recall that the user guide states that index
   register 0 always holds 0).

## Peripherals

1. The description of the audio system describes the existence of a
   microphone.   Can its signal be read by a program?

## Assembly Source

1. How is a not-held instruction (overriding the default for LDE, ITE,
   JPX, JNX) indicated in the symbolic assembler input?  I was unable
   to find an example.
2. Is there a difference between the configuration values 34 and -3?
   Both seem to occur in symbolic code (e.g. the examples memo by
   H. Philip Peterson, 6M-5780, July 23, 1958).
3. The user handbook (ch. 6) appears to state that it is possible to
   assemble an instruction into both the left and right halves of a
   word.  Is the operand address portion of both instructions
   discarded?  If not, how is it handled?
