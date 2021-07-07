#ifndef {{syncset}}_ROS_H
#define {{syncset}}_ROS_H

/* Initialize ROS node.
 *
 * Returns nonzero on success, zero on failure. */
int init_ros(void);

/* Cleanup ROS node. */
void free_ros(void);

/* Give the ROS node a change to process messages.
 *
 * If blocking is true, block until a SMEDL event comes, process it, then
 * return. If blocking is false, process all currently pending events and then
 * return.
 *
 * Returns nonzero on success, zero on failure. */
int run_ros(int blocking);

/* Event forwarding functions - Send an asynchronous event from the ROS node.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.exported_channels(syncset).keys() %}
int forward_ros_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

#endif /* {{syncset}}_ROS_H */
