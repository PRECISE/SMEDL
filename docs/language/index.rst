SMEDL Specification Language
============================

A SMEDL monitoring system is designed at two levels: the monitor level and the
architecture level.

* Monitor specifications describe a single monitor, that is,
  a list of state variables, a list of events that the monitor consumes and
  emits (known as "imported" and "exported" events), and a set of states,
  transitions, and actions describing the state machine.
* Architecture specifications describe how multiple monitors come together to
  form a monitoring system, including which monitor specifications are
  involved, how instances of the monitors are parameterized, and how imported
  and exported events are directed.

Monitor specifications are written in ``.smedl`` files, and there may be
multiple in a monitoring system. Architecture specifications are written in
``.a4smedl`` files, and there is exactly one per monitoring system.

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   smedl
   a4smedl
