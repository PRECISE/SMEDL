Comparator2
===========

This monitor system is intended primarily to test SMEDL's features. It reads
nextInt, nextFloat, nextChar, nextString, nextPointer, and nextOpaque events
and 1) initializes a new monitor with that identity, and 2) sends it to all
existing monitors. The existing monitors compare the received value against the
previous value and emit match() if they match, mismatch() if they do not. Each
monitor reaches a final state after two comparisons.
