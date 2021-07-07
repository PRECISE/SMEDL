Full API
========

.. default-domain:: c

.. note::

   Many file names and identifiers in this API contain placeholders for event,
   monitor, and synchronous set names. These placeholders are marked by the use
   of ALLCAPS.

Note that most programs will not need to interact with the portions of the API
not described on the :doc:`api` page. Developers not interfacing with SMEDL on
a low level can safely skip this page. In any case, be sure to read that page
before continuing here, as it contains some useful information about the code
in general that is not reproduced below.

The rest of this page is dedicated to describing the full API at each level of
a SMEDL monitoring system.

Monitor
-------

**Header:** ``MONSPEC_mon.h``

.. struct:: MONSPECMonitor

   A monitor instance. Should be obtained from :func:`init_MONSPEC_monitor`
   and exported event callbacks registered with :func:`register_MONSPEC_EVENT`.
   Cleanup callback can be set with :func:`registercleanup_MONSPEC`.

.. function:: int init_MONSPEC_monitor(SMEDLValue *identities)

   Return a new monitor instance. When no longer needed, it should be freed
   with :func:`free_MONSPEC_monitor`.

   :param identities: Array of identities for this monitor instance
   :return: Nonzero for success, zero for malloc failure

.. TODO remove later*

.. function:: void free_MONSPEC_monitor(MONSPECMonitor *mon)

   Free a monitor instance. **Note:** Does not free the monitor identities!
   That must be done by the caller, if necessary.

   :param mon: Monitor instance to free

.. function:: void register_MONSPEC_EVENT(MONSPECMonitor *mon, \
   int (*cb_func)(SMEDLValue *, SMEDLValue *, void *))

   Set the callback for an exported event, called when that event is raised.

   :param mon: Monitor instance to set callback for
   :param cleanup_func: Pointer to callback function. Must accept monitor
                        identities, event parameters, and aux pointer as
                        parameters and return nonzero/zero for success/error

.. TODO remove later*

.. function:: void registercleanup_MONSPEC(MONSPECMonitor *mon, \
   int (*cleanup_func)(MONSPECMonitor *))

   Set the callback for monitor cleanup, called when the monitor instance
   reaches all its final states.

   :param mon: Monitor instance to set callback for
   :param cleanup_func: Pointer to callback function. Must accept a monitor
                        pointer and return nonzero/zero for success/error.

.. TODO remove later*

.. function:: int setvar_MONSPEC_STATEVAR(MONSPECMonitor *mon, \
   SMEDLValue value)

   Set a state variable. Intended to be used only on a newly created monitor
   instance to initialize a state variable to a non-default value.

   :param mon: Monitor instance to set the state variable for
   :param value: Value to assign to the state variable
   :return: Nonzero for success, zero for malloc failure

.. TODO remove later*

.. function:: int execute_MONSPEC_EVENT(MONSPECMonitor *mon, \
   SMEDLValue *params, void *aux)

   Import an event into this monitor. The event is immediately handled. This
   function returns once the macro step is complete—that is, once this event
   and any internal and exported event it causes have been handled or exported.

   :param mon: Monitor instance to handle the event
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.
   :return: Nonzero for success, zero for error

   Note that when an event handler fails, it means the monitor is no longer
   consistent with its specification, has very possible dropped events, and is
   likely to misbehave when handling future events. However, it is still safe
   to free the instance, and it will not leak memory as long as that is done.

.. TODO remove later*

Local Wrapper
-------------

**Header:** ``MONITOR_local_wrapper.h``

.. function:: int init_MONITOR_local_wrapper(void)

   Initialize this local wrapper. Must be called before any other functions in
   the local wrapper.

   :return: Nonzero for success, zero for error

.. function:: void free_MONITOR_local_wrapper(void)

   Tear down and free the resources used by this local wrapper and all the
   monitors it manages

.. function:: int create_MONITOR(SMEDLValue *identities)

   Create a new instance of the monitor with the given identities. If a monitor
   with the given identities already exists, do nothing.

   :param identities: Array of monitor identities
   :return: Nonzero for success, zero for error

.. TODO remove later*

.. function:: int set_MONITOR_STATEVAR(SMEDLValue *identities, \
   SMEDLValue value)

   Set the value of a state variable on the monitor with the given identities.
   Intended to be used only on a newly created monitor instance to initialize a
   state variable to a non-default value.

   :param identities: Array of monitor identities for the instance to modify
   :param value: Value to assign to the state variable
   :return: Nonzero for success, zero for error

.. TODO remove later*

.. function:: int perform_MONITOR_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Send this event to the monitor instances matching the identities. If there
   are no wildcards in the identities and the instance does not exist yet,
   dynamically instantiate it.

   :param identities: Array of monitor identities. Wildcard identities are
                      represented by a :struct:`SMEDLValue` with type
                      :enumerator:`SMEDL_NULL`. **Note:** Using wildcards for
                      identities where there was no wildcard in the
                      architecture specification will result in undefined
                      behavior.
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.
   :return: Nonzero for success, zero for error

Global Wrapper
--------------

**Header:** ``SYNCSET_global_wrapper.h``

.. function:: int init_SYNCSET_syncset(void)

   Initialize this global wrapper and all local wrappers within. Must be called
   before any other functions in the global wrapper.

   :return: Nonzero for success, zero for error

.. function:: void free_SYNCSET_syncset(void)

   Tear down and free all the resources used by this global wrapper and the
   local wrappers and monitors within

.. function:: int run_SYNCSET(void)

   Process all currently queued events from PEDL and the manager. Normally
   should be called after every call to :func:`forward_SYNCSET_EVENT`. Returns
   once there are no more events queued, including events raised by monitors in
   response.

.. function:: int raise_MONITOR_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Queue an exported event from one of the monitors in this synchronous set.
   Returns right away.

   :param identities: Array of identities of the exporting monitor instance
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.
   :return: Nonzero for success, zero for error

.. TODO remove later*

.. function:: int raise_pedl_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Queue an incoming PEDL event. Returns right away. It will be processed when
   the manager calls :func:`run_SYNCSET`, which happens when the target program
   calls :func:`run_manager`.

   :param identities: This parameter is provided for consistency with other
                      event passing functions. It is ignored and may safely be
                      set to NULL.
   :param params: Array of event parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.
   :return: Nonzero for success, zero for error

.. TODO remove later*

.. function:: int forward_SYNCSET_MONITOR_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Queue an incoming asynchronous event. "MONITOR" and "EVENT" in this case
   refer to the source monitor and event (or ``pedl`` if the source was a PEDL
   event). Actual processing does not happen until the manager calls
   :func:`run_SYNCSET`, which should generally happen after every call to one
   of these functions.

   :param identities: Array of the source monitor's identities. Ignored for
                      PEDL events and may be safely set to NULL.
   :param params: Array of source event's parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.

.. TODO remove later*

Manager
-------

**Header:** ``SYNCSET_manager.h``

.. function:: int init_manager(void)

   Initialize SMEDL: manager, attached global wrapper, all local wrappers and
   monitors beneath it, and any transport adapter.

   :return: Nonzero for success, zero for error

.. function:: void free_manager(void)

   Destroy all monitors and wrappers, close all connections, and free the
   resources used by SMEDL. May be called if SMEDL monitoring is no longer
   required.

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

.. function:: int report_MONITOR_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Queue an event from the global wrapper to be forwarded to the transport
   adapter or vice versa.

   :param identities: Array of source monitor identities
   :param params: Array of source event parameters
   :param aux: Auxiliary data pointer, passed through to events raised as a
               result of this one.

.. TODO remove later*

Transport Adapter
-----------------

**Header:** ``SYNCSET_TRANSPORT.h``

Transport adapters are intended to present an API to the manager that's similar
to the global wrapper. There are only a couple differences:

1. Whenever there is a ``SYNCSET`` placeholder in the global wrapper, the name
   of the transport is used instead (e.g. ``rabbitmq``, ``ros``).

2. The :func:`run_TRANSPORT` function accepts a parameter for blocking or
   nonblocking. The global wrapper can always process all queued events
   immediately, so it never blocks. Transport adapters may need to wait for
   incoming events to arrive. See the description for that function for more
   info.

.. function:: int init_TRANSPORT(void)

   Initialize this transport adapter. Must be called before any other
   functions in the transport adapter.

   :return: Nonzero for success, zero for error

.. function:: void free_TRANSPORT(void)

   Close all connections and free all the resources used by this transport
   adapter.

.. function:: int run_TRANSPORT(int blocking)

   Process all currently queued events from the manager and receive any events
   pending from the network. Can be used in two modes: blocking and
   nonblocking.

   Blocking mode is intended for synchronous sets without PEDL events. Since
   these synchronous sets normally run in their own process, it is best to
   block while waiting for the next event to arrive.

   Nonblocking mode is intended for synchronous sets that do have PEDL events.
   SMEDL does not want to be an unnecessary bottleneck for the target program,
   so it returns when the next asynchronous event has not arrived yet.

   :param blocking: Nonzero to run in blocking mode, zero to run in nonblocking
                    mode.
   :return: Nonzero for success, zero for error.

.. function:: int forward_TRANSPORT_MONITOR_EVENT(SMEDLValue *identities, \
   SMEDLValue *params, void *aux)

   Emit an asynchronous event over this transport. "MONITOR" and "EVENT" in
   this case refer to the source monitor and event (or ``pedl`` if the source
   was a PEDL event).

   :param identities: Array of the source monitor's identities. Ignored for
                      PEDL events and may be safely set to NULL.
   :param params: Array of source event's parameters
   :param aux: Auxiliary data pointer. Some transports expect the pointed-to
               data to have a certain structure. Can be set to NULL if not
               required.

.. TODO remove later*
