#ifndef EVENTS_H
#define EVENTS_H

#include "smedl_types.h"

/* Represents an event queued within a monitor for handling */
typedef struct Event {
    int event;
    /* params is an array. Size is known because number of parameters for any
     * specified event is known. */
    SMEDLValue *params;
    Aux aux;
    struct Event *next;
} Event;

/* Represents an event queued in a global wrapper for dispatching */
typedef struct GlobalEvent {
    Event a; /* a.next is ignored */
    int mon;
    /* ids (monitor identities) is an array. Size is known because the number of
     * identities for a specified monitor is known. */
    SMEDLValue *ids;
    struct GlobalEvent *next;
} GlobalEvent;

#endif //EVENTS_H
