#include "smedl_types.h"
#include "global_wrapper.h"
#include "{{syncset}}_global_wrapper.h"
{% for decl in mon_decls %}
#include "{{decl.name}}_local_wrapper.h"
{% endfor %}


{% for decl in mon_decls %}
{% if loop.first %}
/* Callback function pointers */
{% endif %}
{% for target in decl.connections.values() if target.monitor is none %}
static SMEDLCallback cb_{{target.channel}};
{% endfor %}
{% endfor %}

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. */
void init_{{syncset}}_syncset() {
    {% for decl in mon_decls %}
    init_{{decl.name}}_local_wrapper();
    {% endfor %}
    //TODO Anything else?
}

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages */
void free_{{syncset}}_syncset() {
    {% for decl in mon_decls %}
    free_{{decl.name}}_local_wrapper();
    {% endfor %}
    //TODO Anything else?
}

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

void raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    //TODO
}
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
{% macro import_handler(target) %}
    {% if target.mon_params is nonempty %}
    SMEDLValue new_identities[{{len(target.mon_params)}}] = {
            {% for param in target.mon_params %}
            {% if param.index is none %}
            {SMEDL_NULL},
            {% elif param.identity %}
            identities[{{param.index}}],
            {% else %}
            params[{{param.index}}],
            {% endif %}
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_identities = NULL;
    {% endif %}

    {% if target.target_type == 'creation' %}
    {{sys.monitor_decls[target.monitor].spec.name}}State init_state;
    default_{{sys.monitor_decls[target.monitor].spec.name}}_state(&init_state);
    {% for var, param in target.state_vars.items() %}
    init_state.{{var}}_var = {%+ if param.identity -%}
        identities[{{param.index}}]
        {%- else -%}
        params[{{param.index}}]
        {%- endif -%}
        .v.
        {%- if param_type is sameas SmedlType.INT -%}
            i
        {%- elif param_type is sameas SmedlType.FLOAT -%}
            d
        {%- elif param_type is sameas SmedlType.CHAR -%}
            c
        {%- elif param_type is sameas SmedlType.STRING -%}
            s
        {%- elif param_type is sameas SmedlType.POINTER -%}
            p
        {%- elif param_type is sameas SmedlType.THREAD -%}
            th
        {%- elif param_type is sameas SmedlType.OPAQUE -%}
            o
        {%- endif %};
    {% endfor %}

    create_{{target.monitor}}_monitor(new_identities, &init_state);
    {% elif target.target_type == 'event' %}
    {% if target.event_params is nonempty %}
    SMEDLValue new_params[{{len(target.event_params)}}] = {
            {% for param in target.event_params %}
            {% if param.identity %}
            identities[{{param.index}}],
            {% else %}
            params[{{param.index}}],
            {% endif %}
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_params = NULL;
    {% endif %}

    process_{{target.monitor}}_{{target.event}}(new_identities, new_params, aux);
    {% endif %}
{%- endmacro %}
{# Events from target system #}
{% for target in system.imported_connections.values() if target.monitor in system.syncsets[syncset] %}

void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    {{import_handler(target)}}

    //TODO call queue processing function
}
{% endfor %}
{# Events from other synchronous sets #}
{% for decl in system.monitor_decls if decl.syncset != syncset %}
{% for target in decl.connections.values() if target.monitor in system.syncsets[syncset] %}

void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    {{import_handler(target)}}

    //TODO call queue processing function
}
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
 *   a SMEDLAux for passthrough data. */
{% for decl in mon_decls %}
{% for target in decl.connections.values() if target.monitor is none %}

void callback_{{syncset}}_{{target.channel}}(SMEDLCallback cb_func) {
    cb_{{target.channel}} = cb_func;
}
{% endfor %}
{% endfor %}
