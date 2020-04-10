#ifndef {{syncset}}_GLOBAL_WRAPPER_H
#define {{syncset}}_GLOBAL_WRAPPER_H

#include "smedl_types.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. */
void init_{{syncset}}_syncset();

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages */
void free_{{syncset}}_syncset();

/* Global wrapper export interfaces - Called by monitors to place exported
 * events into the appropriate export queues, where they will later be routed to
 * the proper destinations inside and outside the synchronous set.
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
void raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux);
{% endfor %}
{% endfor %}

/* Global wrapper import interface - Called by the environment (other
 * synchronous sets, the target system) to import events into this global
 * wrapper. Each connection that this synchronous set receives has a separate
 * function.
 *
 * Parameters:
 * identities - An array of the source monitor's identities. If the connection
 *   is from the target system, this parameter is ignored and can safely be set
 *   to NULL.
 * params - An array of the source event's parameters
 * aux - Extra data to be passed through unchanged */
{# Events from target system #}
{% for target in system.imported_connections.values() if target.monitor in system.syncsets[syncset] %}
void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux);
{% endfor %}
{# Events from other synchronous sets #}
{% for decl in system.monitor_decls if decl.syncset != syncset %}
{% for target in decl.connections.values() if target.monitor in system.syncsets[syncset] %}
void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux);
{% endfor %}
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
 *   a SMEDLAux for passthrough data.
 *
 * TODO Should we create a way to explicitly export events to the target system
 * in the architecture file? This would allow 1) sending events to both a
 * monitor and the target system and 2) Assigning an explicit channel name. The
 * auto-generated channel names are "_<monitor>_<event>". A possible syntax
 * might be like "ch_name: SourceMon.source_event => env;". If we do this, we
 * should likely prohibit connections that go directly from the target system to
 * the target system, as no synchronous set will take ownership of routing it
 * when none of their monitors are involved.
 */
{% for decl in mon_decls %}
{% for target in decl.connections.values() if target.monitor is none %}
void callback_{{syncset}}_{{target.channel}}(void (*cb_func)(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux));
{% endfor %}
{% endfor %}

/* NOTE: The API document calls for a "PEDL" interface in the global wrapper,
 * but I don't recall coming to a definite conclusion on how to address the
 * coexistence of the PEDL interface and synchronous sets. As best I remember,
 * the closest we came was deciding that one synchronous set should be
 * responsible for that, and it should get a dummy synchronous set if not
 * assigned otherwise, but I don't remember specifying how that should fit into
 * the architecture file format. Until that is cleared up, the PEDL interface is
 * on hold.
 */

/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/

#endif /* {{syncset}}_GLOBAL_WRAPPER_H */
