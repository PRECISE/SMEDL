#include <stdlib.h>
#include "smedl_types.h"
#include "events.h"

/* Add an event to the queue. Return 1 if successful, 0 if malloc fails.
 *
 * Parameters:
 * q - Pointer to the EventQueue to push to
 * event - Event ID (from one of the monitors' event enums)
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_event(EventQueue *q, int event, SMEDLValue *params, Aux aux) {
    /* Create the Event */
    Event *e = malloc(sizeof(Event));
    if (e == NULL) {
        return 0;
    }
    e->event = event;
    e->params = params;
    e->aux = aux;
    e->next = NULL;

    /* Add it to the queue */
    if (q->head == NULL) {
        q->head = e;
    } else {
        q->tail->next = e;
    }
    q->tail = e;
    return 1;
}

/* Remove an event from the queue. Return 1 if successful, 0 if the queue is
 * empty.
 *
 * Parameters:
 * q - Pointer to the EventQueue to pop from
 * event - Pointer to store the event ID at
 * params - Pointer at which to store an array of the event's parameters
 * aux - Pointer to an Aux struct to store the aux data in */
int pop_event(EventQueue *q, int *event, SMEDLValue **params, Aux *aux) {
    /* Check if queue is empty */
    if (q->head == NULL) {
        return 0;
    }

    /* Pop the head of the queue */
    Event *e = q->head;
    q->head = e->next;
    if (q->head == NULL) {
        q->tail = NULL;
    }

    /* Store the values in the pointer params */
    *event = e->event;
    *params = e->params;
    *aux = e->aux;

    free(e);
    return 1;
}

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
        int event, SMEDLValue *params, Aux aux) {
    /* Create the GlobalEvent */
    GlobalEvent *ge = malloc(sizeof(GlobalEvent));
    if (ge == NULL) {
        return 0;
    }
    ge->e.event = event;
    ge->e.params = params;
    ge->e.aux = aux;
    ge->mon = mon;
    ge->ids = ids;
    ge->next = NULL;

    /* Add it to the queue */
    if (q->head == NULL) {
        q->head = ge;
    } else {
        q->tail->next = ge;
    }
    q->tail = ge;
    return 1;
}

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
        int *event, SMEDLValue **params, Aux *aux) {
    /* Check if queue is empty */
    if (q->head == NULL) {
        return 0;
    }

    /* Pop the head of the queue */
    GlobalEvent *ge = q->head;
    q->head = ge->next;
    if (q->head == NULL) {
        q->tail = NULL;
    }

    /* Store the values in the pointer params */
    *event = ge->e.event;
    *params = ge->e.params;
    *aux = ge->e.aux;
    *mon = ge->mon;
    *ids = ge->ids;

    free(ge);
    return 1;
}
