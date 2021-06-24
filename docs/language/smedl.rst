SMEDL Specifications
====================

.. highlight:: smedl

A SMEDL specification consists of a declaration and three sections: state
variables (which is optional), event declarations, and scenarios.

The declaration is a single line naming the monitor, for example::

    object NoLightWeakUntilButton;

Identifiers in SMEDL follow nearly the same rules as in C:

* The first character must be a lowercase or uppercase letter
* Characters after may be letters, numbers, or underscore

The only difference from C is that they cannot start with an underscore. (Such
identifiers are reserved for SMEDL's internal use.)

The rest of the sections are described below.

.. _state_vars:

State Variables
---------------

This section declares the state variables and their initial values::

    state:
      int light = 0;
      int button = 0;

State variables can be used in the conditions and actions for a transition.
They can be of the following types (as can any value in SMEDL):

=========== =============== ============== ====================================
Type        C Equivalent    Default        Description
                            Initial Value
=========== =============== ============== ====================================
``int``     ``int``         ``0``          Integer
``float``   ``double``      ``0.0``        Double precision floating point
``double``                                 Alias for ``float``
``char``    ``char``        ``'\0'``       Character or Byte
``string``  ``char *``      ``""``         Null-terminated string
``pointer`` ``void *``      ``NULL``       Pointer
``opaque``  ``SMEDLOpaque`` ``{.data=NULL, Opaque data of known size
                            .size=0}``
=========== =============== ============== ====================================

.. note::

   Opaque vs. Pointer
     While opaques contain a ``void *``, the actual value is the data pointed
     to. It is assumed that the data can be safely copied (e.g. it does not
     contain self-referential pointers). Whereas for pointers, the pointer
     itself is the value.

   Opaque vs. String
     Opaques are of a known size, good for representing an arbitrary array or
     struct. They may contain null bytes. Strings may not contain null bytes,
     since the null-terminator is used to determine their length.

Initial values can be omitted, in which case, default initial values will be
used::

    state:
      int light;
      int button;

If there are no state variables, the section can be left out entirely.

Event Declarations
------------------

The event declarations section defines the events that the monitor works with
and their parameters::

    events:
      imported light_is(int);
      imported button_is(int);
      internal check();
      exported satisfaction();
      exported violation();

If an event has multiple parameters, they are separated by commas::

    imported foo(string, int);

There are three types of events:

``imported``
  Events received from outside this monitor. They may be used to trigger
  transitions.

``exported``
  Events emitted from this monitor. They can be raised in transition actions.
  (They can also act as internal events, if that would be convenient.)

``internal``
  Events raised in one scenario and received by another within the same
  monitor. They cannot enter nor leave the monitor.

Event parameters use the same types described under :ref:`state_vars`.

Scenarios
---------

The scenarios section describes the actual state machines that make up the
monitor::

    scenarios:
      input:
        idle -> light_is(status) {
            light = status;
            raise check();
          } -> idle;
        idle -> button_is(status) {
            button = status;
            raise check();
          } -> idle;

      verify:
        waiting
          -> check() when (!light && !button)
          -> waiting;
        waiting
          -> check() when (button) {raise satisfaction();}
          -> satisfied;
          else {raise violation();}
          -> violated;
        satisfied -> check() -> satisfied;
        violated -> check() -> violated;

This example contains two scenarios, labeled ``input`` and ``verify``. Each
scenario is a separate state machine.

Each scenario is defined as a list of transitions. Each transition contains a
start state, one or more events, an end state, and an optional else clause::

    <start-state> -> <event>(<params>) [when (<condition>)] [{<actions>}]
                 [-> <event>(<params>) [when (<condition>)] [{<actions>}]]
                  ...
                  -> <end-state>
                 [else [{<actions>}] -> <else-state>] ;

.. TODO

Additional Features
-------------------

.. TODO helper function includes
.. TODO whitespace

Examples
--------

Here is an example of a simple monitor that emits a running total each time it
receives a measurement::

    object Adder;

    state:
      float accumulator = 0;

    events:
      imported measurement(float);
      exported sum(float);

    scenarios:
      main:
        idle
          -> measurement(val) {
            accumulator = accumulator + val;
            raise sum(accumulator);
          }
          -> idle;

Here is a more advanced monitor, used for the snippets above. It verifies that
a light does not turn on until a button is pressed::

    object NoLightWeakUntilButton;

    state:
      int light = 0;
      int button = 0;

    events:
      imported light_is(int);
      imported button_is(int);
      internal check();
      exported satisfaction();
      exported violation();

    scenarios:
      input:
        idle -> light_is(status) {
            light = status;
            raise check();
          } -> idle;
        idle -> button_is(status) {
            button = status;
            raise check();
          } -> idle;

      verify:
        waiting
          -> check() when (!light && !button)
          -> waiting;
        waiting
          -> check() when (button) {raise satisfaction();}
          -> satisfied;
          else {raise violation();}
          -> violated;
        satisfied -> check() -> satisfied;
        violated -> check() -> violated;
