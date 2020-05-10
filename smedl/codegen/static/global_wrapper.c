#include <stdlib.h>
#include "smedl_types.h"
#include "monitor.h"
#include "global_wrapper.h"

/* Add an event to the queue. Return 1 if successful, 0 if malloc fails.
 *
 * Parameters:
 * q - Pointer to the EventQueue to push to
 * channel - Channel ID (from the global wrapper's channel enum)
 * ids - Array of the monitor's identities
 * params - Array of the event's parameters
 * aux - Aux data to pass through */
int push_global_event(GlobalEventQueue *q, unsigned int channel,
        SMEDLValue *ids, SMEDLValue *params, SMEDLAux aux) {
    /* Create the GlobalEvent */
    GlobalEvent *ge = malloc(sizeof(GlobalEvent));
    if (ge == NULL) {
        return 0;
    }
    ge->channel = channel;
    ge->ids = ids;
    ge->params = params;
    ge->aux = aux;
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
 * channel - Pointer to store the channel ID at
 * ids - Pointer at which to store an array of the monitor identities
 * params - Pointer at which to store an array of the event's parameters
 * aux - Pointer to an Aux struct to store the aux data in */
int pop_global_event(GlobalEventQueue *q, unsigned int *channel,
        SMEDLValue **ids, SMEDLValue **params, SMEDLAux *aux) {
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
    *channel = ge->channel;
    *ids = ge->ids;
    *params = ge->params;
    *aux = ge->aux;

    free(ge);
    return 1;
}
