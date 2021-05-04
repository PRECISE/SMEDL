#ifndef {{mon.name}}_LOCAL_WRAPPER_H
#define {{mon.name}}_LOCAL_WRAPPER_H

#include <stdint.h>
#include "smedl_types.h"
#include "monitor_map.h"
#include "{{spec.name}}_mon.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the local wrapper. Must be called once
 * before creating any monitors or importing any events.
 * Return nonzero on success, zero on failure. */
int init_{{mon.name}}_local_wrapper();

/* Cleanup interface - Tear down and free the resources used by this local
 * wrapper and all the monitors it manages */
void free_{{mon.name}}_local_wrapper();

/* Creation interface - Instantiate a new {{mon.name}} monitor.
 * Return nonzero on success or if monitor already exists, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * init_state - A pointer to a {{spec.name}}State containing
 *   the initial state variable values for this monitor. A default initial
 *   state can be retrieved with default_{{spec.name}}_state()
 *   and then just the desired variables can be updated. */
int create_{{mon.name}}_monitor(SMEDLValue *identities, {{spec.name}}State *init_state);

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 * Return nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * params - An array of SMEDLValue, one for each parameter of the event.
 * aux - Extra data that is passed through to exported events unchanged. */
{% for event in spec.imported_events.keys() %}
int process_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/
{% if mon.params is nonempty %}

/* Recycle a monitor instance - Used as the callback for when final states are
 * reached in the monitor. Return nonzero if successful, zero on failure. */
int recycle_{{mon.name}}_monitor({{spec.name}}Monitor *mon);

/* Add the provided monitor to the monitor maps. Return a
 * MonitorInstance, or NULL if unsuccessful. */
MonitorInstance * add_{{mon.name}}_monitor({{spec.name}}Monitor *mon);

/* Fetch a list of monitor instances matching the given identities.
 *
 * Identities are given as an array of SMEDLValue. Wildcards for multicast
 * are indicated with SMEDLValues with type SMEDL_NULL.
 *
 * If there are no matching monitor instances but the identity list is fully
 * specified (i.e. there are no wildcards), create an instance with those
 * identities and return it.
 *
 * Returns a linked list of MonitorInstance (which may be empty, i.e. NULL).
 * If dynamic instantiation fails, returns INVALID_INSTANCE. */
MonitorInstance * get_{{mon.name}}_monitors(SMEDLValue *identities);

#endif /* {{mon.name}}_LOCAL_WRAPPER_H */
