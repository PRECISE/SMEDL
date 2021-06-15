#ifndef {{syncset}}_GLOBAL_WRAPPER_H
#define {{syncset}}_GLOBAL_WRAPPER_H

#include "smedl_types.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. Return nonzero on success, zero on failure. */
int init_{{syncset}}_syncset(void);

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages. */
void free_{{syncset}}_syncset(void);

/* Run interface - Process all currently-queued events. Should be called after
 * every call to forward_*().
 * TODO Name conflict if syncset is named "manager"
 *
 * Returns nonzero on success, zero on failure. */
int run_{{syncset}}(void);

/* Global wrapper export interface - Called by monitors and the target program
 * to raise events for the global wrapper to process.
 *
 * When called by the target program, actual processing does not happen until
 * run_{{syncset}}() is called, but the target program should not call
 * it directly. Instead, it should call run_manager() and the manager will
 * invoke run_{{syncset}}() as necessary.
 *
 * Returns nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for the exporting
 *   monitor. Ignored for events from the target program and may be set to
 *   NULL.
 * params - An array of SMEDLValue, one for each parameter of the exported event
 * aux - Extra data that was passed from the imported event that caused this
 *   exported event
 */
{% for decl in mon_decls %}
{% for event in decl.spec.exported_events.keys() %}
int raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}
{% for event, conn in sys.ev_imported_connections.items() if conn.syncset.name == syncset %}
int raise_pedl_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/* Global wrapper import interface - Called by an external module (e.g. the
 * manager) to forward events to the global wrapper to be imported by monitors
 * or sent back to the target program. Actual processing does not happen until
 * run_{{syncset}}() is called. To preserve semantics, run_{{syncset}}()
 * should be called after each call to one of these functions.
 *
 * Returns nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for the exporting
 *   monitor. Ignored for events from the target program and may be set to
 *   NULL.
 * params - An array of SMEDLValue, one for each parameter of the exported event
 * aux - Extra data that was passed from the imported event that caused this
 *   exported event
 */
{% for conn in sys.imported_channels(syncset) %}
int forward_{{syncset}}_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/

/* Routing functions - One for each event this synchronous set touches. Called
 * to route each event from the queue appropriately to one or more of monitors,
 * the target program, and the manager.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.connections.values() %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}
{% for conn in pedl_in %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/* Local wrapper and PEDL handoff functions - Take queued event parameters and
 * transform them for the imported monitor event or exported PEDL event, then
 * call the local wrapper or PEDL function.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn, targets in sys.dest_channels(syncset).items() %}
{% for target in targets %}
{% if target.target_type == 'creation' %}
int localcreation_{{conn.channel}}_{{target.mon_string}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% else %}
int local_{{conn.channel}}_{{target.mon_string}}_{{target.event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endif %}
{% endfor %}
{% endfor %}

#endif /* {{syncset}}_GLOBAL_WRAPPER_H */
