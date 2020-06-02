#ifndef SYSTEM_H
#define SYSTEM_H

/* System-wide channel enum */
typedef enum {
    {% for channel in sys.imported_connections.keys() %}
    SYSCHANNEL_{{channel}},
    {% endfor %}
    {% for decl in mon_decls %}
    {% for channel in decl.connections.keys() %}
    SYSCHANNEL_{{channel}},
    {% endfor %}
    {% endfor %}
} ChannelID;

/* System-wide event queue item */
typedef struct SystemEvent {
    ChannelID channel;
    SMEDLValue *identities;
    SMEDLValue *params;
    void *aux;
    struct SystemEvent *next;
} SystemEvent;

/* System-wide event queue */
typedef struct SystemEventQueue {
    SystemEvent *head;
    SystemEvent *tail;
} SystemEventQueue;

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
        SMEDLValue *identities, SMEDLValue *params, void *aux);

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
        SMEDLValue **identities, SMEDLValue **params, void **aux);

#endif /* SYSTEM_H */
