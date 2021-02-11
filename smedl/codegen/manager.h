#ifndef {{syncset}}_MANAGER_H
#define {{syncset}}_MANAGER_H

#include "smedl_types.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the manager and the attached global
 * wrapper and network interfaces.
 *
 * Returns nonzero on success, zero on failure. */
int init_manager(void);

/* Cleanup interface - Tear down and free resources used by the manager and the
 * global wrapper and network interfaces attached to it. */
void free_manager(void);

/* Run interface - Process all pending events in all attached synchronous sets
 * and network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
int run_manager(void);

/* Manager queueing interfaces - Queue events to be forwarded to monitors or
 * network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}
int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/

/* Queue processing function - Deliver the events in the manager queue to their
 * destinations.
 *
 * Returns nonzero on success and zero on failure. */
int process_queue(void);

/* Manager routing functions - One for each event entering or leaving the
 * synchronous set. Called to route each event from the queue appropriately to
 * the global wrapper or network interfaces.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}
int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

#endif /* {{syncset}}_MANAGER_H */
