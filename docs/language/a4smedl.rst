Architecture Specifications
===========================

.. highlight:: a4smedl

A SMEDL monitoring system contains a number of SMEDL monitors that pass events
between each other and the target system. The architecture specification
describes the monitor specifications used in the monitoring system, how those
specifications are parameterized, and how events are passed between them.

The file consists of a list of declarations, the first being the name of the
monitor system itself::

    system NestedCommands;

As with SMEDL specifications, C-style ``/* ... */`` and ``// ...`` comments are
supported, whitespace is ignored except as a word separator, and identifiers
follow nearly the same rules as in C:

* The first character must be a lowercase or uppercase letter
* Characters after may be letters, numbers, or underscore

The rest of the declarations are described below.

Monitor Imports
---------------

SMEDL specifications must be imported before they can be used::

    import "first_command.smedl";
    import "command_pair.smedl";

This makes the monitors specified in these files available to be declared (see
:ref:`mondecl`). Paths are relative to the directory where the architecture
specification resides.

.. _mondecl:

Monitor Declarations
--------------------

Monitors must be declared to make them part of the monitoring system. This
allows monitors to be parameterized::

    monitor FirstCommand(int);
    monitor CommandPair(int, int);

Monitor parameters are sometimes referred to as "identities" since they can be
used to identify a particular instance. Monitors can also be declared
parameterless::

    monitor Frontend();

Parameterless monitors have one instance, created and destroyed along with the
entire monitoring system. For example, they might be used to aggregate events
from parameterized monitors. Parameterized monitors have no instances at first,
but can be instantiated by events. For example, a monitor for connections
might be parameterized by the connection ID, and get instantiated whenever a
"new connection" event arrives.

In either case, the SMEDL specification must be imported before the monitor can
be declared. The monitor name must match the object declaration from the SMEDL
specification, but it can be renamed with the ``as`` modifier::

    monitor FirstCommand(int) as FC;

This is particularly useful for reusing the same specification in two different
monitor declarations. For example, if you had a generic SMEDL specification
that keeps a moving average, you might want to reuse it for different purposes
within your monitoring system. That is possible like this::

    monitor MovingAverage() as RPMAverage;
    monitor MovingAverage() as ThrottleAverage;

Parameters have the same types as any other SMEDL value. See :ref:`types`.

.. warning::

   Using ``float`` and ``opaque`` types as parameters should be done with care.
   SMEDL uses hashtables to store monitor instances, and the hash function for
   all types is based on the underlying bit representation. For ``opaque``,
   this means the underlying data must be comparable with ``memcmp()``, a
   potential issue if the ``opaque`` is filled from a struct with padding
   bytes. For ``float``, apart from the usual caveats with rounding error,
   alternative representations that compare equal may not have the same hash
   value (e.g. +0 and -0).

Event Declarations
------------------

Events to and from monitors are declared in their SMEDL specification. PEDL
events???that is, events to and from the target system???have no such declaration.
Generally, this is not a problem. SMEDL can infer their parameter types based
on the monitor events they are connected to. But if SMEDL would infer
incorrectly (e.g. a PEDL event parameter needs to be an ``int`` for some
reason, but it's passed to a ``float`` parameter at the receiving event), they
can be declared in the architecture::

    imported foo(int);
    exported bar(string, int);

Imported events are from the target system to SMEDL, and exported events vice
versa.

If a PEDL event is declared, it must be declared before it is put into a
synchronous set or used in a connection.

Synchronous Set Definitions
---------------------------

Synchronous sets determine when an event is passed synchronously vs.
asynchronously. Within a synchronous set, events are passed synchronously. Any
event passed between synchronous sets is sent asynchronously.

A synchronous set definition looks like this::

    syncset Commands {FirstCommand, CommandPair, pedl};

In this case, a synchronous set named ``Commands`` is declared to contain
monitors ``FirstCommand`` and ``CommandPair``. The keyword ``pedl`` means any
PEDL events that are not otherwise added to a synchronous set get put in this
one. Here, by placing all monitors *and* PEDL into a single synchronous set, the
entire monitor system is synchronous.

PEDL events can also be put into synchronous sets individually. The
``imported`` and ``exported`` are used to do so::

    syncset Commands {FirstCommand, CommandPair, imported command,
        imported succeed, exported violation};

Any monitor not put into a synchronous set will be implicitly put in its own
synchronous set. If there are any PEDL events not placed in a synchronous set
(and no synchronous set contains the ``pedl`` keyword), a separate ``pedl``
synchronous set is implicitly created. It follows that if no synchronous sets
are defined explicitly, all events will be passed asynchronously.

When code is generated, all monitors in a synchronous set become part of the
same executable. The source of any PEDL events in the synchronous set normally
must be linked in as well, so that is something to be aware of if the target
system consists of multiple processes.

Connection (a.k.a. "Channel") Definitions
-----------------------------------------

Connection definitions are the main purpose of the architecture file: to
specify how the events between monitors and the target system are linked. Here
are several examples::

    cmd1: command => FirstCommand[*].command($0);
    cmd1: command => FirstCommand($0);
    cmd2: FirstCommand.second_command => CommandPair(#0, $0);
    succ: succeed => CommandPair[*, $0].second_success();
    succ: succeed => CommandPair[$0, *].first_success();
    succ: succeed => FirstCommand[$0].success();
    out: CommandPair.violation => violation(#0, #1);

The very simplest connections might look like this::

    MonA.foo => MonB.bar;   // Monitor to Monitor
    foo => MonB.bar;        // PEDL to Monitor
    pedl.foo => MonB.bar;   // PEDL to Monitor
    MonA.foo => bar;        // Monitor to PEDL
    MonA.foo => pedl.bar;   // Monitor to PEDL

The left side of a connection is always an exported monitor event or an
imported PEDL event. The right side is either an imported monitor event, an
exported PEDL event, or a monitor creation event (only the first two are in the
previous example). A PEDL event cannot be connected directly to a PEDL event.

Connections are normally given names::

    foobar: MonA.foo => MonB.bar;
    foo_in: foo => MonB.bar;
    ch3: MonA.foo => bar;

The names are used occasionally in the code, primarily in the transport
adapters, e.g. the channel name for RabbitMQ or the topic name for ROS.

If the destination monitor or event have parameters, the connection needs to
specify how to fill them (otherwise, empty brackets and parentheses are
optional)::

    foobar: MonA.foo => MonB[#0, $0].bar(#0, $1);
    foobar: MonA.foo => MonB[Id.0, Param.0].bar(Id.0, Param.1);

Parameters can come from the source monitor or from the source event. The
former are specified with ``Id.<num>`` or ``#<num>`` and the latter with
``Param.<num>`` or ``$<num>``. The above two lines are equivalent.

The same source event can be sent to multiple destinations by using it in
multiple connections. When doing this, the connection name need not be repeated
each time, but it cannot be changed::

    // Allowed:
    foobar: MonA.foo => MonB[#0].bar($0);
    foobar: MonA.foo => MonC.baz(#0);

    // Allowed:
    foobar: MonA.foo => MonB[#0].bar($0);
    MonA.foo => MonC.baz(#0);

    // Allowed:
    MonA.foo => MonB[#0].bar($0);
    foobar: MonA.foo => MonC.baz(#0);

    // NOT allowed:
    foobar: MonA.foo => MonB[#0].bar($0);
    foobaz: MonA.foo => MonC.baz(#0);

Unicast and Multicast
~~~~~~~~~~~~~~~~~~~~~

Wildcards can be used in the destination monitor parameters, which creates a
multicast connection::

    foobar: MonA.foo => MonB[*, *].bar(#0, $1);
    baz_in: baz => MonB[$0, *].bar();

Unicast and multicast connections are fundamentally different. Unicast
connections send the event to the specific instance identified by a full set of
identities. If that instance does not exist, it is *dynamically instantiated*
on the fly before the event is sent. Multicast connections send the event to
any monitors that match the non-wildcard identities. If no such monitor exists,
nothing happens.

Explicit Creation
~~~~~~~~~~~~~~~~~

The last type of connection is an explicit creation event and it looks like
these::

    foo: MonA.foo => MonB(#0, $0);
    bar: bar => MonB($0, $1, some_var=$2);

These create a new instance of ``MonB`` explicitly. Wildcard parameters are not
allowed. The second line shows an additional shortcut that is possible with
explicit creation: state variable initializers can be added to the end of the
parameter list. These override the default initial values for the given state
variables.

Note that explicit creation and exported PEDL events use similar syntax. If
it's ever ambiguous which is intended (that is, a monitor and PEDL event share
the same name), explicit creation takes priority. Use the ``pedl.`` prefix to
force an exported PEDL event.

Implicit PEDL Exports
~~~~~~~~~~~~~~~~~~~~~

Any events exported by a monitor that aren't used in a connection explicitly
are assumed to be intended for the target system. Thus, implicit exported PEDL
events are created for them, and implicit connections made between the exported
monitor event and the exported PEDL event. The parameters for the PEDL event
will match the parameters for the monitor event.

Examples
--------

Here is an example architecture specification for monitoring online auctions::

    system Auction;

    import "auctionmonitor.smedl";

    monitor Auctionmonitor(string);

    // Params: item name, reserve, duration
    imported new_auction(string, float, int);
    // Params: item name, amount
    imported bid(string, float);
    // Params: item_name
    imported sold(string);
    imported endOfDay();

    ch1: new_auction => Auctionmonitor($0, reserve=$1, duration=$2);
    ch2: bid => Auctionmonitor[$0].bid($1);
    ch3: sold => Auctionmonitor[$0].sold();
    ch4: endOfDay => Auctionmonitor[*].end_of_day;

The goal is to ensure bids monotonically increase, items never sell before
meeting reserve, and items never sell after a certain number of days pass.

* There is a single monitor specification, with a new instance created for each
  item whenever a ``new_auction`` event comes. Explicit creation is used so the
  reserve and duration variables can be initialized.
* ``bid`` and ``sold`` events go to the specific instance for the item they
  refer to.
* ``endOfDay`` events go to all instances because of the wildcard. That way,
  they can all tick off another day from their duration and expire if
  necessary. If there are no auctions yet, nothing happens.
* There are no connections for exported PEDL events, but since none of the
  monitor's exported events are part of a connection, implicit PEDL events will
  be created for all of them.

Here is another architecture specification that several snippets above came
from::

    system NestedCommands;

    import "first_command.smedl";
    import "command_pair.smedl";

    monitor FirstCommand(int);
    monitor CommandPair(int, int);

    syncset Commands {FirstCommand, CommandPair, pedl};

    cmd1: command => FirstCommand[*].command($0);
    cmd1: command => FirstCommand($0);
    cmd2: FirstCommand.second_command => CommandPair(#0, $0);
    succ: succeed => CommandPair[*, $0].second_success();
    succ: succeed => CommandPair[$0, *].first_success();
    succ: succeed => FirstCommand[$0].success();
    out: CommandPair.violation => violation(#0, #1);

The goal here is to validate that if command *X* starts after command *Y*, then
command *X* must succeed before command *Y*.

* Each new command that comes causes a ``FirstCommand`` to be created *and* is
  sent to all existing ``FirstCommand`` as a second command.
* Every time an existing ``FirstCommand`` receives a command, it emits
  ``second_command``, which creates a ``CommandPair``
* Every ``success`` event is sent to all ``CommandPair`` where the first
  command matches as ``first_success`` and all ``CommandPair`` where the second
  command matches as ``second_success``. Each ``CommandPair`` can raise a
  ``violation`` event if its successes some out of order.
* Every ``success`` is also sent to the matching ``FirstCommand``, so it can
  enter its final state and be deallocated.

More examples can be found in the "tests/monitors" directory.
