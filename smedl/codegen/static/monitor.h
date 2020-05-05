#ifndef MONITOR_H
#define MONITOR_H

#include "smedl_types.h"

/* An event in an EventQueue */
typedef struct Event {
    unsigned int event;
    /* params is an array. Size is known because number of parameters for any
     * specified event is known. */
    SMEDLValue *params;
    SMEDLAux aux;
    struct Event *next;
} Event;

/* A queue of events to be handled within a monitor. Initialize both elements
 * to NULL before using. */
typedef struct EventQueue {
    Event *head;
    Event *tail;
} EventQueue;

/* Add an event to the queue. Return 1 if successful, 0 if malloc fails.
 *
 * Parameters:
 * q - Pointer to the EventQueue to push to
 * event - Event ID (from one of the monitors' event enums)
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_event(EventQueue *q, int event, SMEDLValue *params, SMEDLAux aux);

/* Remove an event from the queue. Return 1 if successful, 0 if the queue is
 * empty.
 *
 * Parameters:
 * q - Pointer to the EventQueue to pop from
 * event - Pointer to store the event ID at
 * params - Pointer at which to store an array of the event's parameters
 * aux - Pointer to an Aux struct to store the aux data in */
int pop_event(EventQueue *q, int *event, SMEDLValue **params, SMEDLAux *aux);

#endif /* MONITOR_H */
