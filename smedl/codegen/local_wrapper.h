#ifndef {{mon.name}}_LOCAL_WRAPPER_H
#define {{mon.name}}_LOCAL_WRAPPER_H

#include <stdint.h>
#include "smedl_types.h"
#include "local_wrapper.h"
#include "{{spec.name}}_mon.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the local wrapper. Must be called once
 * before creating any monitors or importing any events. */
void init_{{mon.name}}_local_wrapper();

/* Cleanup interface - Tear down and free the resources used by this local
 * wrapper and all the monitors it manages */
void free_{{mon.name}}_local_wrapper();

/* Creation interface - Instantiate a new {{mon.name}} monitor.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * init_state - A pointer to a {{spec.name}}State containing
 *   the initial state variable values for this monitor. A default initial
 *   state can be retrieved with default_{{spec.name}}_state()
 *   and then just the desired variables can be updated. */
void create_{{mon.name}}_monitor(SMEDLValue *identities, {{spec.name}}State *init_state);

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * params - An array of SMEDLValue, one for each parameter of the event.
 * aux - Extra data that is passed through to exported events unchanged. */
{% for event in spec.imported_events.keys() %}
void process_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux);
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

/* Add the provided monitor to the monitor maps */
void add_{{mon.name}}_monitor({{spec.name}}Monitor *mon);

/* Fetch a list of monitor instances matching the given identities.
 *
 * Identities are given as an array of SMEDLValue. Wildcards for multicast
 * are indicated with SMEDLValues with type SMEDL_NULL.
 *
 * If there are no matching monitor instances but the identity list is fully
 * specified (i.e. there are no wildcards), create an instance with those
 * identities and return it.
 *
 * Returns a linked list of {{mon.name}}Record. */
{{mon.name}}Record * get_{{mon.name}}_monitors(SMEDLValue *identities);

/* Check if a monitor with the given identities is present. Return nonzero if
 * so, zero if not. */
int check_{{mon.name}}_monitors(SMEDLValue *identities);

/* Remove a monitor with the given identities from the monitor maps */
void remove_{{mon.name}}_monitor(SMEDLValue *identities);
{% endif %}

#endif /* {{mon.name}}_LOCAL_WRAPPER_H */
