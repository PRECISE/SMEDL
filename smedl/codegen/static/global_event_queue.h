#ifndef GLOBAL_EVENT_QUEUE_H
#define GLOBAL_EVENT_QUEUE_H

#include "smedl_types.h"

/* Represents an event queued in a global wrapper for dispatching */
typedef struct GlobalEvent {
    unsigned int channel;
    /* ids (monitor identities) is an array. Size is known because the number of
     * identities for a specified monitor is known. */
    SMEDLValue *ids;
    /* Same for params (event parameters) */
    SMEDLValue *params;
    void *aux;
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
 * channel - Channel ID (from the global wrapper's channel enum)
 * ids - Array of the monitor's identities
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_global_event(GlobalEventQueue *q, unsigned int channel,
        SMEDLValue *ids, SMEDLValue *params, void *aux);

/* Remove an event from the queue. Return 1 if successful, 0 if the queue is
 * empty.
 *
 * Parameters:
 * q - Pointer to the EventQueue to pop from
 * channel - Pointer to store the channel ID at
 * ids - Pointer at which to store an array of the monitor identities
 * params - Pointer at which to store an array of the event's parameters
 * aux - Pointer to an Aux pointer to store the aux data in */
int pop_global_event(GlobalEventQueue *q, unsigned int *channel,
        SMEDLValue **ids, SMEDLValue **params, void **aux);

#endif /* GLOBAL_EVENT_QUEUE_H */
