TODO
====

Final and Error States
------------

Final states are not currently implemented. They need to be added back in. Error
states also need to be implemented, though they were new even to SMEDL 1.x.

Semantics Details
-----------------

### Monitor Semantics

- Monitors do not currently block attempts to import events while the macro-step
  for the previous imported event is still processing. Such a check should not
  be difficult to add, but need to consider whether the import call should block
  (and blocked imports unblock in the order they were called) or not (simply
  returning unsuccessfully). Or should that be a configurable option?
  * Note that this is not a problem when monitors are used with the local/global
    wrappers. They are currently written such that they will wait for a monitor
    to return from its macro-step before doing further processing. This would
    definitely need revisiting, however, if we implement some sort of
    concurrency.
  * This makes monitors not thread-safe. But if we assume the target is single-
    threaded (or only calling the monitor from a single thread), the only other
    place where this could become an issue is with exported events. When an
    event is exported, it calls a callback. Nothing is preventing that callback
    from triggering another imported event before it returns to let the macro-
    step finish. The local/global wrappers do not do this, but if we use a
    monitor without the wrappers, there is no guarantee.
  * See also the "Concurrency and Thread Safety" section, as these issues are
    sort of related.
- Monitors emit exported events as they are raised. This may not be in agreement
  with the semantics. But, it may not actually matter if further events cannot
  be imported until the current macro-step is complete (so in fact, it might
  agree with the semantics after all).
- According to the current semantics, all events exported in a macro-step should
  be a set, implying that there are no duplicates. We do not currently check
  for this.
  * If we do start checking, should such events still trigger scenarios
    twice, like duplicate internal events would? I would assume so. (One use for
    duplicate internal events: counting.)
  * If we did not allow this, there would then be the question of when the event
    should be processed: in its original slot or in the latter slot.
  * If we do want to implement this (i.e., don't change the set to a multiset in
    the semantics), the best way would likely be to place exported events in a
    second queue in addition to the regular event queue, and whenever adding an
    event to the export queue, check for duplicates. Additional overhead would
    be a practical consequence of this. A combination hashtable/linked list or
    balanced tree/linked list would be a good idea.

### Synchronous Set Semantics

- Similar to monitors, the global wrapper does not currently block attempts to
  import events while it is still processing the previous imported event. This
  is not an issue when using the RabbitMQ adapter, but when using synchronous
  communication, can pose a problem. See also the "Concurrency and Thread
  Safety" sections, as these issues are sort of related.
- The global wrapper does not do any sort of event ordering or reordering.
  Consider a Monitor 1 that exports an event that both Monitor 2A and Monitor 2B
  receive. Monitor 2A exports an event connected to the creation of Monitor 3,
  and monitor 2B exports a multicast event imported by Monitor 3. Thus, it would
  be ideal if the event from Monitor 1 is processed by 2A before 2B, ensuring
  that Monitor 3 is created before the multicast event goes out. However, the
  global wrapper does no such enforcement, and it is currently arbitrary whether
  Monitor 2A or 2B runs first.
  * Currently, it is up to the user writing the monitors to ensure that such
    cases will not have a negative impact on monitoring. I am not sure if a goal
    of the semantics would be to catch such situations and either warn about or
    prohibit them.
  * For that matter, a similar thing can happen with multiple scenarios within a
    monitor, and we do not detect that either.

Concurrency and Thread Safety
-----------------------------

- All processing within a synchronous set is currently single-threaded. This
  could likely be improved, but we must be careful not to break the semantics.
  Adding a mutex to the monitor object would likely help, but need to consider
  when to lock and unlock it and if one mutex per monitor is sufficient and/or
  flexible enough. See also the first bullet point under "Semantics Details"
  (about blocking imported events during a macro-step).
- Similarly, SMEDL is not thread-safe. Mutexes are likely the solution to this,
  as well.
