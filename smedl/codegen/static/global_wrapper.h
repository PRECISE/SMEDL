#ifndef GLOBAL_WRAPPER_H
#define GLOBAL_WRAPPER_H

#include "smedl_types.h"
#include "monitor.h"

/* Represents an event queued in a global wrapper for dispatching */
typedef struct GlobalEvent {
    Event e; /* e.next is ignored */
    unsigned int mon;
    /* ids (monitor identities) is an array. Size is known because the number of
     * identities for a specified monitor is known. */
    SMEDLValue *ids;
    struct GlobalEvent *next;
} GlobalEvent;

/* A queue of events in a global wrapper. Initialize both elements to NULL
 * before using. */
typedef struct GlobalEventQueue {
    GlobalEvent *head;
    GlobalEvent *tail;
} GlobalEventQueue;

/* Add an event to the queue. Return 1 if successful, 0 if malloc fails.
 *
 * Parameters:
 * q - Pointer to the EventQueue to push to
 * mon - Monitor ID (from the global wrapper's monitor enum)
 * ids - Array of the monitor's identities
 * event - Event ID (from one of the monitors' event enums)
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_global_event(GlobalEventQueue *q, int mon, SMEDLValue *ids,
        int event, SMEDLValue *params, SMEDLAux aux);

/* Remove an event from the queue. Return 1 if successful, 0 if the queue is
 * empty.
 *
 * Parameters:
 * q - Pointer to the EventQueue to pop from
 * mon - Pointer to store the monitor ID at
 * ids - Pointer at which to store an array of the monitor identities
 * event - Pointer to store the event ID at
 * params - Pointer at which to store an array of the event's parameters
 * aux - Pointer to an Aux struct to store the aux data in */
int pop_global_event(GlobalEventQueue *q, int *mon, SMEDLValue **ids,
        int *event, SMEDLValue **params, SMEDLAux *aux);

#endif /* GLOBAL_WRAPPER_H */
