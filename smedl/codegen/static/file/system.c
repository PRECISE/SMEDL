#include <stdlib.h>
#include "smedl_types.h"
#include "system.h"

/* Add an event to the queue. Return nonzero if successful, zero if malloc
 * fails.
 *
 * Parameters:
 * q - Pointer to the SystemEventQueue to push to
 * channel - ChannelID for the event
 * identities - Array of SMEDLValue for monitor identities (ignored if there
 *   are none or the event is from the target system)
 * params - Array of SMEDLValue for the event parameters
 * aux - Aux data to pass through */
int push_system_event(SystemEventQueue *q, ChannelID channel,
        SMEDLValue *identities, SMEDLValue *params, void *aux) {
    /* Create the SystemEvent */
    SystemEvent *e = malloc(sizeof(SystemEvent));
    if (e == NULL) {
        return 0;
    }
    e->channel = channel;
    e->identities = identities;
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

/* Remove an event to the queue. Return nonzero if successful, zero if malloc
 * fails.
 *
 * Parameters:
 * q - Pointer to the SystemEventQueue to pop from
 * channel - Pointer to store the ChannelID at
 * identities - Pointer at which to store an array of SMEDLValue for monitor
 *   identities (must be provided but can be ignored if there are none)
 * params - Pointer at which to store an array of SMEDLValue for the event
 *   parameters
 * aux - Pointer at which to store passed through aux data */
int pop_system_event(SystemEventQueue *q, ChannelID *channel,
        SMEDLValue **identities, SMEDLValue **params, void **aux) {
    /* Check if queue is empty */
    if (q->head == NULL) {
        return 0;
    }

    /* Pop the head of the queue */
    SystemEvent *e = q->head;
    q->head = e->next;
    if (q->head == NULL) {
        q->tail = NULL;
    }

    /* Store the values in the pointer params */
    *channel = e->channel;
    *identities = e->identities;
    *params = e->params;
    *aux = e->aux;

    free(e);
    return 1;
}
