# Compound Characters

Compound chars are described in item 7 on page 607 of the TX-2 Users
Handbook (Nov 63).

Compound characters are described like so:

- Only one backspace
- Two or three characters only.
- Space bar is allowed
- Any sequence of characters is legal. (Except ...)

This seems confusing at first but the key to understanding it is that
the Lincoln Writer (from which these characters come) has four
characters which don't advance the carriage when they are printed
(underline, overline, square, circle).  That is, the following
character is overstruck.  The underline _ is one such character: then
_ followed by G is a compound character, _ overstruck with G.  This
would be a two-character compound character.

A compound character can also be formed with a space, presumably for
example a character which doesn't advance the carriage followed by a
space, which does.

Using our single allowed backspace, we could create a compound
character using a character which does advance the carriage, for
example K.  K\b> K overstruck with a >.

Another three-character option is to use two non-carriage-advancing
characters.  The documentation doesn't seem to clearly state whether
Lincoln Writer codes 0o74 and 0o75 ("LOWER CASE" and "UPPER CASE") are
permitted.  This makes a difference because for example CIRCLE is
upper case while SQUARE is lower case (both signaled by code 013).  So
I am not clear on whether this sequence of codes is a valid single
compound character (assume we start in upper-case).

Code  | Representing          | Advances carriage?
----- | ------------          | ------------------
013   | CIRCLE                | No (it's special)
074   | Shift to lower case   | No (it's non-printing)
013   | SQUARE                | No (it's special)
057   | *                     | Yes (rightward)

If valid this would represent a circle, square and asterisk all on the
same spot.

we didn't need to worry much about this, because we cannot tell the
difference; the current parser implementation accepts Unicode input,
and by the time the Lincoln Writer code have been translated into
Unicode, the upper/lower case shift codes are no longer present in the
parser's input.


Another input that tests our understanding is this one:

Code  | Representing          | Advances carriage?
----- | ------------          | ------------------
013   | CIRCLE                | No (it's special)
062   | Backspace             | Yes (leftward!)
012   | _ (underline)         | No (it's special)

This meets the letter of the condition (just one backspace,
only three characters).  But the net effect of these code is a
net leftward movement of the carriage/cursor.

Yet another:

Code  | Representing          | Advances carriage?
----- | ------------          | ------------------
031   | J                     | Yes
062   | Backspace             | Yes (leftward!)
027   | H                     | Yes
062   | Backspace             | Yes (leftward!)
032   | K                     | Yes

Here we apparently see 031 062 027 as the first compound
character (three characters, one backspace) but is the
following thing valid?  The problem is it starts with a
backspace.  That cannot be part of the initial compound
character because only one backspace is allowed.

## Interpretation of the M4 Description in the Users Handbook

It seems that the Users Handbook underspecifies the compound
character.  We will have to do something - accept some inputs and
perhaps reject others.

I plan to add additional restrictions, not stated in the
Users Handbook, which helps disambiguate:

A compound character is a sequene of two or three characters
which

1. Does not begin with a backspace
2. Does not end with a backspace
3. Does not end with a dead character (a character which does
   not advance the carriage).
4. Includes either a backspace or a dead character.

The thinking behind this restriction is that it enforces a
requirement that the "compound character" not overlap with
those characters that precede or follow it.

If D represents a non-advancing character (_, square, and so
on), X represents a character which does advance the carriage,
S represents space and \b represents backspace, these are
valid compound characters:

- DS
- DX
- S\bX
- X\bS
- S\bS (more about this one below)
- DDS
- DDX

In terms of error-handling, once we see a dead character at the
current input position, we know that we need to end up with a compound
character which starts with it.  Once we see a regular character which
advances the carriage followed by a backspace, we know we must be
looking at a three-character compound character (i.e. it's an error
for the character after the \b to be a dead character).

The following examples would not be valid because the above rule
disallows them.  After each I identify in parentheses the reason I
think it should not be allowed (i.e. why our additional restriction is
helpful).

- XX\b (would overlap the next character)
- DDD  (would overlap the next character)
- DXD  (would overlap the next character)
- DSD  (would overlap the next character)
- DDD  (would overlap the next character)
- SDD  (would overlap the next character)
- XDD  (would overlap the next character)
- \bDX (would overlap the previous character)
- \bXX (similar, but also visually appears to be two characters).

These rules permit the form "S\bS" even though that's potentially
confusing for users in that it is visually insidtinguishable from a
single space.

Condition 4 above ensures that these forms are not considered compound
characters:

- XX  (we want to parse that as two simple characters)
- XXX (we want to parse that as three simple characters)
- XSX (we want to parse that as two single-character syllables
  separated by a space)
- XDX (we want to parse this as the simple character X followed by the
  compound character DX, because this reflects the fact that the
  syllable takes up two "columns")

This overstriking behaviour is described by A. Vanderburgh
in "The Lincoln Keyboard - a typewriter keyboard designed
for computers imput flexibility", a one-page paper in
Communications of the ACM, Volume 1, Issue 7, July 1958
(https://doi.org/10.1145/368873.368879).


## Difficulty of Supporting Compound Characters for Unicode Input

Our previous support for processing of the underline, overline, aquare
and circle overstrike characters was based on the use of the following
Unicode characters:

Unicode | TX-2 | Description
U+0332  | 012  | combining low line
U+0305  | 012  | combining overline
U+20DD  | 013  | combining enclosing circle
U+20DE  | 013  | combining enclosing square

There are two characters each for 012 and 013 as these differ in case.

This Unicode equivalence strategy is flawed.  In Unicode, these
combining characters follow the character with which they combine.  In
the TX-2 Lincoln Writer, they precede them.  So we cannot just convert
directly in a kind of naive way.  So for the humans' representation of
this I think we're going to have to use markup.  Meanwhile I will
remove support for non-carriage-advancing characters (like the above)
and overstruck compoung characters (using a backspace).
