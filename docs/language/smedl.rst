SMEDL Specifications
====================

.. highlight:: smedl

A SMEDL specification consists of a declaration, optional helper includes, and
three sections: state variables (which is optional), event declarations, and
scenarios. C-style ``/* ... */`` and ``// ...`` comments are supported, and
whitespace is ignored except as a word separator.

The declaration is a single line naming the monitor, for example::

    object NoLightWeakUntilButton;

Identifiers in SMEDL follow nearly the same rules as in C:

* The first character must be a lowercase or uppercase letter
* Characters after may be letters, numbers, or underscore

The only difference from C is that they cannot start with an underscore. (Such
identifiers are reserved for SMEDL's internal use.)

The rest of the sections are described below.

State Variables
---------------

This section declares the state variables and their initial values::

    state:
      int light = 0;
      int button = 0;

State variables can be used in the conditions and actions for a transition.
They can have any of the six types SMEDL recognizes (see :ref:`types`). Initial
values can be omitted::

    state:
      int light;
      int button;

In that case, default initial values will be used:

=========== =========================
SMEDL Type  Default Initial Value
=========== =========================
``int``     ``0``
``float``   ``0.0``
``char``    ``'\0'``
``string``  ``""``
``pointer`` ``NULL``
``opaque``  ``{.data=NULL, .size=0}``
=========== =========================

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

Event parameters can be any of the SMEDL types (see :ref:`types`) .If an event
has multiple parameters, they are separated by commas::

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
        inconclusive
          -> check() when (!light && !button)
          -> inconclusive;
        inconclusive
          -> check() when (button) {raise satisfaction();}
          -> satisfied;
          else {raise violation();}
          -> violated;
        satisfied -> check() -> satisfied;
        violated -> check() -> violated;

That example contains two scenarios, labeled ``input`` and ``verify``. Each
scenario is a separate state machine.

Each scenario is defined as a list of transitions. Each transition contains a
start state, one or more events, an end state, and an optional else clause::

    <start-state> -> <event>(<params>) [when (<condition>)] [{<actions>}]
                 [-> <event>(<params>) [when (<condition>)] [{<actions>}]]
                  ...
                  -> <end-state>
                 [else [{<actions>}] -> <else-state>] ;

The first transition's start state becomes the initial state for the entire
scenario.

A very simple transition could look like this::

    locked -> auth() -> unlocked;

If the ``auth`` event arrives while the scenario is in the ``locked`` state, it
transitions to the ``unlocked`` state.

Transitions can also have conditions::

    locked -> auth_with_pin(code) when (code == 12345) -> unlocked;

The ``auth_with_pin`` event will be ignored from the ``locked`` state unless
the condition is true. Conditions can be any valid expression that's not of
type ``string`` or ``opaque`` (see :ref:`expressions`). They can make use of
state variables and the event's parameters, and their truthiness is evaluated
according to C rules: zero and NULL are false, anything else is true.

Transitions can have actions that execute when the transition is taken. Actions
are used to modify state variables or raise internal and exported events (see
:ref:`actions` for the full list)::

    locked -> auth_with_pin(code) when (code == 12345) {
            unlock_count++;
            raise audit_unlock(code, unlock_count);
        } -> unlocked;

Multiple transitions can have the same event from the same start state with
different conditions. The first transition that matches will be taken. For
example::

    locked -> auth_with_pin(code) when (code == 12345) -> unlocked;
    locked -> auth_with_pin(code) when (code == 67890) -> unlocked_admin;

An else clause on a transition specifies which state to transition to when the
start state and event match, but the condition does not. It can optionally
contain actions as well::

    locked -> auth_with_pin(code) when (code == 12345) -> unlocked
        else {raise audit_denial(code);} -> locked;

When there are multiple transitions with the same start state and event, only
one of them may contain an else clause. That else clause applies only if *none*
of the conditions match, regardless of order. In the following example,
``audit_denial`` is only raised if neither code matches::

    locked -> auth_with_pin(code) when (code == 12345) -> unlocked
        else {raise audit_denial(code);} -> locked;
    locked -> auth_with_pin(code) when (code == 67890) -> unlocked_admin;

Transitions can contain multiple events chained together. In that case, SMEDL
acts as if there is an anonymous implicit state between each chained event::

    locked -> auth_with_pin(code) when (code == 12345)
           -> confirm_auth() -> unlocked;
    locked -> auth_with_pin(code) when (code == 67890) -> unlocked_admin;

Note that the anonymous implicit state between ``auth_with_pin`` and
``confirm_auth`` means that ``auth_with_pin(67890)`` would be ignored if it
came between ``auth_with_pin(12345)`` and ``confirm_auth()``.

An else clause on a transition with chained events applies to every event in
the chain.

.. admonition:: Event Ordering

   An imported event's actions may raise internal and exported events, some of
   which may raise further events. The processing of this entire chain of
   events is known as a *macro step*. Macro steps always run to completion
   before another event is imported.

   Within a macro step, if a single event triggers a simultaneous transition in
   multiple scenarios, either scenario is permitted to run first. However, all
   raised events are processed in the order that they were raised.

   For example, if the actions for ``event_a`` raise ``event_b`` and then
   ``event_c``, both will be queued until ``event_a``'s actions are complete.
   Then, ``event_b`` will be handled, followed by ``event_c``. If ``event_b``'s
   actions raised a fourth event, it would be queued until after ``event_c``.

Final States
------------

Sometimes, when a monitor reaches a certain state, it is known that it has
reached the end of its useful life (e.g. if a monitored connection is closed).
Final states allow such monitors to be deallocated to save memory and CPU
cycles.

One or more scenarios can have a final state declared right after the scenario
label::

    scenarios:
        main:
            finalstate closed;
            pre -> open() -> opened;
            opened -> close() -> closed;

Once the final state is reached, the monitor signals that it can be
deallocated. (When a full monitor system is generated, the local wrapper
handles the actual deallocation.)

If more than one scenario has a final state, they must all be reached before
the monitor signals for deallocation. (Scenarios without final states are
ignored during this check.)

.. _types:

Types
-----

SMEDL uses the following data types:

=========== =============== ====================================
SMEDL Type  C Equivalent    Description
=========== =============== ====================================
``int``     ``int``         Integer
``float``   ``double``      Double precision floating point
``double``                  Alias for ``float``
``char``    ``char``        Character or Byte
``string``  ``char *``      Null-terminated string
``pointer`` ``void *``      Pointer
``opaque``  ``SMEDLOpaque`` Opaque data of known size
=========== =============== ====================================

.. note::

   **Opaque vs. Pointer**
     While opaques contain a ``void *``, the actual value is the data pointed
     to. It is assumed that the data can be safely copied (e.g. it does not
     contain self-referential pointers). Whereas for pointers, the pointer
     itself is the value.

   **Opaque vs. String**
     Opaques are of a known size, good for representing an arbitrary array or
     struct. They may contain null bytes. Strings may not contain null bytes,
     since the null-terminator is used to determine their length.

.. _expressions:

Expressions
-----------

Expressions in SMEDL are very C-like. They can be any of the following:

* Literal

  - Integer literal (decimal, hexadecimal with ``0x``/``0X`` prefix, or octal
    with ``0`` prefix)
  - Floating point literal (decimal, hexadecimal with ``0x``/``0X`` prefix and
    ``p``/``P`` exponent)
  - String literal (double quoted, same backslash escapes as C99)
  - Char literal (single quoted, same backslash escapes as C99)
  - Boolean literal (``true``, ``false``)
  - Null pointer literal (``null``, ``NULL``)

* State variable

* Event parameter

* Helper function call (see :ref:`helpers`)

* Compound expression

  - ``<unary-operator><expression>``
  - ``<expression> <binary-operator> <expression>``

* Parenthesized expression (``(<expression>)``)

The operators available are a subset of C's, all are left associative, and they
have the same precedence as in C:

1. Unary ``+``, unary ``-``, bitwise negation ``~``, logical negation ``!``
2. Multiplication ``*``, division ``/``, modulo ``%``
3. Addition ``+``, subtraction ``-``
4. Left shift ``<<``, right shift ``>>``
5. Less than/or equal ``<`` ``<=``, greater than/or equal ``>`` ``>=``
6. Equal ``==``, not equal ``!=``
7. Bitwise AND ``&``
8. Bitwise XOR ``^``
9. Bitwise OR ``|``
10. Logical AND ``&&``
11. Logical OR ``||``

.. warning::

   Equal/not equal operations on strings and opaques come with some
   caveats.

   1. Opaque equality is based on a byte-by-byte comparison with ``memcmp()``.
      This may not always produce the intended result, e.g. when the opaque is
      filled from a struct with padding bytes. An alternative option is to use
      a helper function that accepts two ``SMEDLOpaque`` and returns zero or
      nonzero (see :ref:`helpers`).

   2. Due to limitations on type verification, ``==`` and ``!=`` may not work
      properly on strings and opaques when *both* sides of the comparison are a
      helper function. SMEDL relies on type checking to determine when to
      generate ``strcmp()`` or ``memcmp()`` instead of plain ``==``/``!=``.
      Unfortunately, since SMEDL cannot verify the types for helper functions,
      when *both* sides are helpers, it must generate plain ``==``/``!=`` by
      default.

.. _helpers:

Helper Functions
~~~~~~~~~~~~~~~~

For operations that SMEDL can't do natively, helper function calls can be used.
For example, if you want to take the sine of a floating point parameter
``angle``, you could do ``sin(angle)``. Helper functions must accept and return
the C equivalent types listed under :ref:`types`, but SMEDL does not verify
this when type checking.

The relevant ``#include`` should be added between the monitor declaration and
state variable section, for example::

    object MyMonitor;

    #include <math.h>

    state:
        ...

.. TODO Add a note somewhere (probably on the page about using mgen) about
   adding the relevant source files to the Makefile

Helper functions are especially useful with the opaque type as a way to operate
on structs and arrays. For example, you might have C code like this to work
with X-Y coordinates:

.. code-block:: c

    // point.c

    #include <math.h>
    #include "smedl_types.h"

    struct point {
        double x;
        double y;
    };

    SMEDLOpaque to_opaque(struct point *p) {
        SMEDLOpaque o;
        o.size = sizeof(*p);
        o.data = p;
        return o;
    }

    struct point to_point(SMEDLOpaque o) {
        return *((struct point *) o.data);
    }

    double distance(SMEDLOpaque o1, SMEDLOpaque o2) {
        struct point p1, p2;
        p1 = to_point(o1);
        p2 = to_point(o2);
        return sqrt(pow(p2.x - p1.x, 2) + pow(p2.y - p1.y, 2))
    }

Then, with ``#include "point.h"``, you have a way to take the distance between
two ``struct point`` in SMEDL.

Helper functions are discouraged from keeping state or having other side
effects.

.. _actions:

Actions
-------

An action can be one of five types of statements:

**Increment**
  ``<state-var>++;`` – Increments a state variable.

**Decrement**
  ``<state-var>--;`` – Decrements a state variable.

**Assignment**
  ``<state-var> = <expression>;`` – Assign the result of the expression to a
  state variable.

**Raise**
  ``raise <event>([<expression>, ...]);`` – Raise an exported or internal
  event.

**Call helper**
  ``<function>([<expression>, ...]);`` – Call a helper function (see
  :ref:`helpers`). This is only useful for helper functions with side effects,
  so ideally, it should be used sparingly.

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

Here is a more advanced monitor, used for some of the snippets above. It
verifies that a light does not turn on until a button is pressed::

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
        inconclusive
          -> check() when (!light && !button)
          -> inconclusive;
        inconclusive
          -> check() when (button) {raise satisfaction();}
          -> satisfied;
          else {raise violation();}
          -> violated;
        satisfied -> check() -> satisfied;
        violated -> check() -> violated;

More examples can be found in the "tests/monitors" directory.
