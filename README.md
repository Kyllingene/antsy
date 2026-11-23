# `antsy` - convenient ANSI string handling

`antsy` provides fully `no_std` utilities for dealing with strings containing
ANSI escape codes. It's useful for e.g. getting the visual length of a string
that's got escape codes internally, or printing such a string with escapes
stripped.

Note that this is not made for interpreting or executing escape codes: it is
meant to allow you to deal with a string as if the escapes weren't there.

## Note on parsing

`antsy` makes two sacrifices to "true" ANSI compatibility:
 - Most modern implementations, while not required, have opted to allow C0
   (`0x00`-`0x1F`) controls to be placed in the middle of another escape code,
   with the effect that the C0 control takes effect immediately upon
   encountering. To achieve this here would either require allocations or to
   parse every individual escape code known to man, which is infeasible. Given
   the fact that internal C0 control codes are an artifact of teletype days, I
   see no reason to change this tradeoff.

 - C1 bytes (`0x9X`, such as for the short version of DCS), are not valid UTF-8.
   To maintain a `str`-based API, I have decided to not support these bytes.
