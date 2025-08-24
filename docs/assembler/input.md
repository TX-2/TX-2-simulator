# Assembler Input Format

Right now the assembler accepts input in Unicode (utf8).  It follows
the conventions of the M4 assembler with respect to the interpretation
of superscripts and subscripts.  However, there are some subscript
characters which exist in M4 which have no equivalent in Unicode.  For
example, Unicode does not have a full set of subscript Latin
characters.

The Nullufy (octal 77) character has no special significance in input
or output.
