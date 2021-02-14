#ifndef {{syncset}}_ASYNC_H
#define {{syncset}}_ASYNC_H

/* Initialize ROS node.
 *
 * Returns nonzero on success, zero on failure. */
int init_async(void);

/* Cleanup ROS node. */
void free_async(void);

/* Give the ROS node a change to process messages.
 *
 * If blocking is true, block until a SMEDL event comes, process it, then
 * return. If blocking is false, process all currently pending events and then
 * return.
 *
 * Returns nonzero on success, zero on failure. */
int run_async(blocking);

/* Event forwarding functions - Send an asynchronous event from the ROS node.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.exported_channels(syncset).keys() %}
int forward_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

#endif /* {{syncset}}_ASYNC_H */
