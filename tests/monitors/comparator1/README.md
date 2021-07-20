Comparator1
===========

This monitor system is intended primarily to test SMEDL's features. It sends
nextString events to one monitor and nextOpaque events to another. Each monitor
checks to see if the string or opaque matches the previous one, and emits an
event to indicate whether it did or not.
