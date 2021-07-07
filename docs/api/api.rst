Essential API
=============

.. default-domain:: c

.. note::

   Many file names and identifiers in this API contain placeholders for event,
   monitor, and synchronous set names. These placeholders are marked by the use
   of ALLCAPS.

The generated monitoring code is separated into multiple layers, ordered below
from lowest to highest. SMEDL specifications are used to generate the monitor
layer, and the rest are generated from the architecture specification.

**Monitor**
  Actual monitor logic for a single SMEDL specification

**Local wrapper**
  Manages instances, does unicast/multicast routing, and dynamic instantiation
  for a single monitor

**Global wrapper**
  Routes events within a single synchronous set to the proper local wrappers or
  PEDL

**Transport adapters**
  A "sibling" of the global wrapper in the hierarchy—sends and receives
  asynchronous events over the selected transport mechanism (RabbitMQ, ROS,
  etc.)

**Manager**
  Initiates event handling at the global wrapper and transport adapters and
  passes asynchronous events between them

Most programs will only need to interact with part of the global wrapper and
manager, so those are the only APIs described on this page. (The full API is
described at :doc:`full_api`.)

Overview
--------

The target program interacts with SMEDL through PEDL events. First, it makes a
function call to emit an event. At that point, the event is queued, but the
call immediately returns. Then, it makes another call to pass control to the
manager. The manager allows all pending synchronous events to be processed and
asynchronous events to be sent. This call returns when there are no more events
immediately left to process (though there may still be asynchronous events
outstanding). Finally, the target program must provide functions of its own for
receiving PEDL events back from the monitors.

By default, SMEDL generates a PEDL stub that reads events from a CSV and does
all of the above. This allows the monitors to be buildable immediately and can
serve as demo code, but most real-world programs will want to replace most or
all of this file with actual instrumentation.

For asynchronous PEDL events (that is, those not explicitly placed in a
synchronous set), SMEDL generates a ``pedl`` synchronous set that does nothing
except send and receive PEDL events asynchronously. This allows for the same
API to be used, regardless of synchronization. But, if convenient, the ``pedl``
synchronous set can be dropped, and the target program or its instrumentation
can send and receive events over the asynchronous message channels directly.
For more information on that, go back to :doc:`index` and visit the page for
the appropriate asynchronous transport.

SMEDL Types
-----------

Most types in SMEDL correspond directly to a well-known type in C (see
:ref:`types`). The exception is the ``opaque`` type, represented in C by
:struct:`SMEDLOpaque` from :file:`smedl_types.h`:

.. struct:: SMEDLOpaque

   C type representing SMEDL's ``opaque`` type

   .. var:: void *data

      Pointer to the opaque's contents

   .. var:: size_t size

      Length of the opaque in bytes

.. TODO remove later*

For situations where C code needs to store or pass SMEDL values of arbitrary
type, there is :struct:`SMEDLValue`, also in :file:`smedl_types.h`:

.. struct:: SMEDLValue

   Represents a SMEDL value of arbitrary type

   .. var:: SMEDLType t

      SMEDL type of this value

   .. union:: v

      Value itself, using the C type matching the :enum:`SMEDLType`

      .. var:: int i

      .. var:: double d

      .. var:: char c

      .. var:: char *s

      .. var:: void *p

      .. var:: SMEDLOpaque o

.. TODO remove later*

For the :var:`~SMEDLValue.t` member, there is a :enum:`SMEDLType` enum:

.. enum:: SMEDLType

   Identifies one of the six SMEDL types

   .. enumerator:: SMEDL_INT

   .. enumerator:: SMEDL_FLOAT

   .. enumerator:: SMEDL_CHAR

   .. enumerator:: SMEDL_STRING

   .. enumerator:: SMEDL_POINTER

   .. enumerator:: SMEDL_OPAQUE

   .. enumerator:: SMEDL_NULL

      Represents a wildcard parameter or a parameter that is irrelevant and
      unknown

.. _event_conventions:

Event Passing Conventions
-------------------------

Many functions in the SMEDL API are used to pass events from one place to
another. For consistency, all of these functions use the same signature:

.. function:: int event_passing_function(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   The signature used by every event-passing function in SMEDL.

   :param identities: An array of monitor identities, either the source monitor
                      (for an exported event) or the destination monitor (for
                      an imported event). If the monitor has no identities or
                      or it is a PEDL event, this parameter is ignored and can
                      be safely set to NULL.
   :param params: An array of the event parameters.
   :param aux: Auxiliary data pointer. When one event causes another to be
               raised, this pointer is passed through untouched. This can be
               used for provenance information or any other purpose. Some
               asynchronous transports expect this to point to a particular
               type of data. NULL is always allowed.
   :return: Nonzero for success, zero for error

.. TODO remove later*

Note that there is no need to specify the length for the :var:`identities` or
:var:`params` parameters since they are known from the architecture
specification.

The convention that SMEDL follows is that the caller retains responsibility for
any allocated memory passed as a parameter. Thus, any event handling function
that receives parameter arrays must make a copy if they need to be retained
after returning, and the same goes for the contents of any string or opaque
values.

Initialization and Cleanup
--------------------------

Before emitting any PEDL events or running the manager, SMEDL must be
initialized. If SMEDL is no longer needed, it can also be deinitialized to free
resources. Both of these functions are in the manager,
:file:`SYNCSET_manager.h`.

.. function:: int init_manager(void)

   Initialize SMEDL. Must be called before any other function in the SMEDL API.

   :return: Nonzero for success, zero for error

.. function:: void free_manager(void)

   Destroy all monitors and wrappers, close all connections, and free the
   resources used by SMEDL. May be called if SMEDL monitoring is no longer
   required.

Emitting PEDL Events
--------------------

PEDL events are sent to PEDL by calling the following function in the global
wrapper, :file:`SYNCSET_global_wrapper.h`:

.. function:: int raise_pedl_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Raise a PEDL event. This function queues the event for later processing and
   immediately returns.

   :param identities: This parameter is provided for consistency with other
                      event passing functions. It is ignored and may safely be
                      set to NULL.
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer. This pointer is passed through to any
               events triggered by this one. This can be used for provenance
               information or any other purpose.
   :return: Nonzero for success, zero for error

.. TODO remove later*

To actually process the event, the program must call :func:`run_manager`.

Receiving PEDL Events
---------------------

Whenever :func:`run_manager` is called, it is possible that there might be some
PEDL events for the target program to receive back. For each PEDL event that
can be received, the target program must provide the following function:

.. function:: int perform_pedl_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Receive a PEDL event. Called by SMEDL whenever a PEDL event needs to be
   returned to the target program.

   :param identities: This parameter is provided for consistency with other
                      event passing functions. It will be set to NULL.
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer. This pointer is passed through directly
               from whatever event triggered this one.
   :return: Nonzero for success, zero for error

.. TODO remove later*

As noted in :ref:`event_conventions`, the parameter array and the contents of
any strings and opaques may become invalid at any point after the function
returns. If they are needed longer than that, be sure to keep a copy.

Running SMEDL
-------------

SMEDL does not process PEDL and asynchronous events as soon as they are queued.
It only happens when initiated by calling the following function in the
manager, :file:`SYNCSET_manager.h`:

.. function:: int run_manager(void)

   Allow SMEDL to run. When called, the following happens:

   1. SMEDL processes any pending PEDL events.

   2. SMEDL processes any events raised as a result. Synchronous events are
      passed to the appropriate destination within the synchronous set.
      Asynchronous events are passed to the transport adapter to be sent
      out. This continues until there are no more events pending in the
      global wrapper.

   3. The transport adapter is given a chance to receive any incoming
      asynchronous events that are ready. These are passed along to the
      global wrapper for processing, and any events raised as a result are
      handled as in #2.

   Then, the function returns.

   :return: Nonzero for success, zero for error
