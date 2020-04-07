The SMEDL and A4SMEDL Monitoring Language
=========================================

TODO

NOTE: In an expression, == on strings normally compares the contents of the
strings, but due to limitations in type verification, this does not happen when
both sides of the == or != are helper functions that return strings. Similar for
opaques.

NOTE: Using floats as identity parameters is experimental at best and should
very likely be avoided. Hashing may not satisfy the invariant that if a == b,
hash(a) == hash(b). And floats must compare exactly equal.
