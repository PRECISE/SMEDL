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
 * identites - An array of SMEDLValue of the proper length for this monitor. */
int create_{{mon.name}}(SMEDLValue *identities);

/* State variable interface - Set the value of the respective state variable.
 * Intended to be used right after monitor creation.
 * Return nonzero on success, zero if the monitor does not exist.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * value - The value to assign to the state variable. */
{% for var_name in spec.state_vars.keys() %}
int set_{{mon.name}}_{{var_name}}(SMEDLValue *identities, SMEDLValue value);
{% endfor %}

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 * Return nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * params - An array of SMEDLValue, one for each parameter of the event.
 * aux - Extra data that is passed through to exported events unchanged. */
{% for event in spec.imported_events.keys() %}
int perform_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/
{% if mon.params is nonempty %}

/* Record type for monitor maps */
typedef struct {{mon.name}}Record {
    SMEDLRecordBase r;
    {{spec.name}}Monitor *mon;
} {{mon.name}}Record;

/* Add the provided monitor to the monitor maps. Return a
 * {{mon.name}}Record, or NULL if unsuccessful. */
{{mon.name}}Record * add_{{mon.name}}_monitor({{spec.name}}Monitor *mon);

/* Fetch a list of monitor instances matching the given identities.
 *
 * Identities are given as an array of SMEDLValue. Wildcards for multicast
 * are indicated with SMEDLValues with type SMEDL_NULL.
 *
 * If there are no matching monitor instances but the identity list is fully
 * specified (i.e. there are no wildcards), create an instance with those
 * identities and return it.
 *
 * Returns a linked list of {{mon.name}}Record (which may be empty, i.e. NULL).
 * If dynamic instantiation fails, returns INVALID_RECORD. */
{{mon.name}}Record * get_{{mon.name}}_monitors(SMEDLValue *identities);

/* Fetch a monitor with the given identities. Identities must be fully
 * specified (i.e. no wildcards) and if the monitor does not exist, return
 * NULL.
 *
 * Returns a pointer to the {{spec.name}}Monitor or NULL.
 */
{{spec.name}}Monitor * getsingle_{{mon.name}}_monitor(SMEDLValue *identities);

/* Check if a monitor with the given identities is present. Return nonzero if
 * so, zero if not. */
int check_{{mon.name}}_monitors(SMEDLValue *identities);

/* Remove a monitor with the given identities from the monitor maps */
void remove_{{mon.name}}_monitor(SMEDLValue *identities);
{% endif %}

#endif /* {{mon.name}}_LOCAL_WRAPPER_H */
