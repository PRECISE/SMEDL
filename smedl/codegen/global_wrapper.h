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

/* Run interface - Process all currently-queued events TODO in which or both
 * directions?
 *
 * Returns nonzero on success, zero on failure. */
int run_{{syncset}}_wrapper();

/* Global wrapper export interface - Called by monitors and the target program
 * to raise events for the global wrapper to process. Actual processing does
 * not happen until run_{{syncset}}_wrapper() is called.
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
 * run_{{syncset}}_wrapper() is called. TODO That's correct, right?
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
//TODO
int forward_{{syncset}}_{{}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

//TODO







/* Global wrapper export interfaces - Called by monitors to place exported
 * events into the appropriate export queues, where they will later be routed to
 * the proper destinations inside and outside the synchronous set.
 * Returns nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for the exporting
 *   monitor
 * params - An array of SMEDLValue, one for each parameter of the exported event
 * aux - Extra data that was passed from the imported event that caused this
 *   exported event
 */
{% for decl in mon_decls %}
{% for event in decl.spec.exported_events.keys() %}
int raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

/* Global wrapper import interface - Called by the environment (other
 * synchronous sets, the target system) to import events into this global
 * wrapper. Each connection that this synchronous set receives has a separate
 * function.
 * Returns nonzero on success, zero on failure.
 *
 * Parameters:
 * identities - An array of the source monitor's identities. If the connection
 *   is from the target system, this parameter is ignored and can safely be set
 *   to NULL.
 * params - An array of the source event's parameters
 * aux - Extra data to be passed through unchanged */
{% for conn in sys.imported_channels(syncset) %}
int import_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

/* Global wrapper callback interface - Used to register callback functions to be
 * called by this global wrapper when it has an event to export to the
 * environment (other synchronous sets, the target system).
 *
 * Parameters:
 * cb_func - A function pointer for the callback to register, or NULL to
 *   unregister a callback. Must accept three parameters: An array of SMEDLValue
 *   for the source monitor's identities (or NULL if the source monitor has
 *   none), another array of SMEDLValue for the source event's parameters, and
 *   a void * for passthrough data. */
{% for decl in mon_decls %}
{% for conn in decl.inter_connections %}
void callback_{{syncset}}_{{conn.channel}}(SMEDLCallback cb_func);
{% endfor %}
{% endfor %}

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/

typedef enum {
    {% for decl in mon_decls %}
    {% for channel in decl.connections.keys() %}
    CHANNEL_{{syncset}}_{{channel}},
    {% endfor %}
    {% endfor %}
} {{syncset}}ChannelID;

/* Intra routing functions - Called by import interface functions and intra
 * queue processing function to route events to the local wrappers.
 * Return nonzero on success, zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.intra_connections %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

#endif /* {{syncset}}_GLOBAL_WRAPPER_H */
