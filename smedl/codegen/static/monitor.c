#include <stdlib.h>
#include "smedl_types.h"
#include "monitor.h"

/* Add an event to the queue. Return 1 if successful, 0 if malloc fails.
 *
 * Parameters:
 * q - Pointer to the EventQueue to push to
 * event - Event ID (from one of the monitors' event enums)
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_event(EventQueue *q, int event, SMEDLValue *params, void *aux) {
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
 * aux - Pointer to an Aux pointer to store the aux data in */
int pop_event(EventQueue *q, int *event, SMEDLValue **params, void **aux) {
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
