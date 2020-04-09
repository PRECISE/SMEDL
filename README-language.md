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

NOTE: Using threads as identity parameters may result in undefined behavior.
There is no portable way to hash `pthread_t`.

NOTE: Opaque type does not allow any operations except == and !=. These
operations do a byte-by-byte comparison with memcmp. If that is not acceptible,
an alternative is to use a helper function that accepts two SMEDLOpaque and
returns zero or nonzero. Note that if opaques cannot be tested for equality with
memcmp, then it is not safe to use them as monitor identities.
