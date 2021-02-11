#ifndef {{syncset}}_GLOBAL_WRAPPER_H
#define {{syncset}}_GLOBAL_WRAPPER_H

#include "smedl_types.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. Return nonzero on success, zero on failure. */
int init_{{syncset}}_syncset();

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages. */
void free_{{syncset}}_syncset();

/* Run interface - Process all currently-queued events.
 * TODO Name conflict if syncset is named "manager"
 *
 * Returns nonzero on success, zero on failure. */
int run_{{syncset}}();

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
{% for event in sys.ev_imported_connections.keys() %}
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
 * the target program, and the manager. */
{% for conn in sys.imported_channels(syncset) %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.connections.values() %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

#endif /* {{syncset}}_GLOBAL_WRAPPER_H */
