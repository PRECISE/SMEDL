#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include "smedl_types.h"
#include "global_event_queue.h"
#include "{{sys.name}}_defs.h"
#include "{{syncset}}_manager.h"
#include "{{syncset}}_global_wrapper.h"
//TODO Next include still needed after switching to set_* interface?
{% for decl in mon_decls %}
#include "{{decl.name}}_local_wrapper.h"
{% endfor %}
{% for spec_name in sys.syncset_spec_names(syncset) %}
#include "{{spec_name}}_mon.h"
{% endfor %}

/* Global event queue - Stores all pending events from all sources: monitors,
 * target program, and manager. */
static GlobalEventQueue queue;

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. Return nonzero on success, zero on failure. */
int init_{{syncset}}_syncset(void) {
    {# No need to initialize intra_queue and inter_queue because they are
        static storage duration (due to being global) thus are initialized to
        NULL automatically #}
    /* Initialize all local wrappers */
    {% for decl in mon_decls %}
    if (!init_{{decl.name}}_local_wrapper()) {
        goto fail_init_{{decl.name}};
    }
    {% endfor %}

    return 1;

    /* Cleanup on failure */
    {% for decl in mon_decls|reverse %}
    {% if not loop.first %}
    free_{{decl.name}}_local_wrapper();
    {% endif %}
fail_init_{{decl.name}}:
    {% endfor %}
    return 0;
}

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages. */
void free_{{syncset}}_syncset(void) {
    /* Free local wrappers */
    {% for decl in mon_decls %}
    free_{{decl.name}}_local_wrapper();
    {% endfor %}
}

/* Run interface - Process all currently-queued events. Should be called after
 * every call to forward_*().
 *
 * Returns nonzero on success, zero on failure. */
int run_{{syncset}}(void) {
    int success = 1;
    int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for conn in sys.imported_channels(syncset) %}
            case CHANNEL_{{conn.channel}}:
                success = route_{{syncset}}_{{conn.channel}}(identities, params, aux) && success;
                //TODO These events were queued from outside. Need to free
                // identities.
                {% for param_type in conn.source_event_params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(params[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(params[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                break;
            {% for decl in mon_decls %}
            {% for conn in decl.connections.values() %}
            case CHANNEL_{{syncset}}_{{conn.channel}}:
                success = route_{{syncset}}_{{conn.channel}}(identities, params, aux) && success;
                {% for param_type in conn.source_event_params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(params[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(params[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                break;
            {% endfor %}
            {% endfor %}
            {% endfor %}
        }

        /* Event params were malloc'd. They are no longer needed. (String and
         * opaque data were already free'd in the switch.) */
        free(params);
    }
    return success;
}

/* Routing functions - One for each event this synchronous set touches. Called
 * to route each event from the queue appropriately to one or more of monitors,
 * the target program, and the manager.
 *
 * Returns nonzero on success, zero on failure. */
{# -------------------------------------------------------------------------- #}
{# Parameters for route macro:
    conn - Connection object to route
    imported - True if this connection is from outside the synchronous set. #}
{% macro route(conn, imported) -%}
#if DEBUG >= 4
fprintf(stderr, "Global wrapper '{{syncset}}' routing for conn '{{conn.channel}}'\n");
#endif
result = 1;

{% set routing = namespace(external=false) %}
{% for target in conn.targets %}
{% if target.syncset.name != syncset %}
{% set routing.external = true %}
{% elif target.target_type == 'creation' %}
result = localcreation_{{conn.channel}}_{{target.mon_string}}(identities, params, aux) && result;
{% else %}
result = local_{{conn.channel}}_{{target.mon_string}}_{{target.event}}(identities, params, aux) && result;
{% endif %}
{% endfor %}

{% if routing.external and not imported %}
result = report_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux) && result;

{% endif %}
return result;
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% for conn in sys.imported_channels(syncset) %}

int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn, true)|indent}}
}
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.connections.values() %}

int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn, false)|indent}}
}
{% endfor %}
{% endfor %}

/* Local wrapper and PEDL handoff functions - Take queued event parameters and
 * transform them for the imported monitor event or exported PEDL event, then
 * call the local wrapper or PEDL function.
 *
 * Returns nonzero on success, zero on failure. */
{# Local/PEDL handoff macros ************************************************ #}
{% macro param_converter(array_name, param, dest_type) -%}
{% if dest_type is sameas param.source_type %}
{{array_name}}[{{param.index}}]
{%- else %}
{{param.source_type}}
{# Numeric types can convert, so we must do that #}
{
    {%- if dest_type is sameas SmedlType.INT -%}
    SMEDL_INT, {.i
    {%- elif dest_type is sameas SmedlType.FLOAT -%}
    SMEDL_FLOAT, {.d
    {%- elif dest_type is sameas SmedlType.FLOAT -%}
    SMEDL_CHAR, {.c
    {%- endif %} = {{array_name}}[{{param.index}}].v.
    {%- if param.source_type is sameas SmedlType.INT -%}
    i}
    {%- elif param.source_type is sameas SmedlType.FLOAT -%}
    d}
    {%- elif param.source_type is sameas SmedlType.CHAR -%}
    c}
    {%- endif %}
}
{%- endif %}
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% macro param_initializer(param, dest_type) -%}
{% if param.index is none %}
{SMEDL_NULL}
{%- elif param.identity %}
{{param_converter("identities", param, dest_type)}}
{%- else %}
{{param_converter("params", param, dest_type)}}
{%- endif %}
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% for conn, targets in dest_channel(syncset).items() %}
{% for target in targets %}

{% if target.target_type == 'creation' %}
int localcreation_{{conn.channel}}_{{target.mon_string}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% if target.mon_params is nonempty %}
    SMEDLValue new_identities[{{target.mon_params|length}}] = {
            {% for param, dest_type in target.mon_params_w_types %}
            {{param_initializer(param, dest_type)|indent(12)}},
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_identities = NULL;
    {% endif %}

    if (!create_{{target.monitor.name}}(new_identities)) {
        /* malloc fail */
        return 0;
    }
    {% for var, param in target.state_vars.items() %}
    {% set array_name = "identities" if param.identity else "params" %}
    if (!set_{{target.monitor.name}}_{{var.name}}(new_identities, {{array_name}}[{{param.index}}])) {
        goto fail;
    }
    {% endfor %}

fail:
    //TODO Need a way to free the created monitor
    return 0;
}
{% else %}
int local_{{conn.channel}}_{{target.mon_string}}_{{target.event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% if target.mon_params is nonempty %}
    SMEDLValue new_identities[{{target.mon_params|length}}] = {
            {% for param, dest_type in target.mon_params_w_types %}
            {{param_initializer(param, dest_type)|indent(12)}},
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_identities = NULL;
    {% endif %}

    {% if target.event_params is nonempty %}
    SMEDLValue new_params[{{target.event_params|length}}] = {
            {% for param, dest_type in target.event_params_w_types %}
            {{param_initializer(param, dest_type)|indent(12)}},
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_params = NULL;
    {% endif %}

    if (!perform_{{target.mon_string}}_{{target.event}}(new_identities, new_params, aux)) {
        /* malloc fail */
        return 0;
    }

    return 1;
}
{% endif %}
{% endfor %}
{% endfor %}

//TODO implement raise_* and forwards_* to queue an event and return

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

int raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% if event in decl.ev_connections %}
    {% set conn = decl.ev_connections[event] %}
    {% set params_len = decl.spec.exported_events[event]|length %}
    SMEDLValue *params_copy = smedl_copy_array(params, {{params_len}});
    if (params_copy == NULL) {
        return 0;
    }
    if (!push_global_event(&queue, CHANNEL_{{conn.channel}}, identities, params_copy, aux)) {
        smedl_free_array(params_copy, {{params_len}});
        return 0;
    }
    return 1;
    {% else %}
    // Event not routed anywhere
    return 1;
    {% endif %}
}
{% endfor %}
{% endfor %}
{% for event, conn in sys.ev_imported_connections.items() if conn.syncset.name == syncset %}

int raise_pedl_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% set params_len = conn.source_event_params|length %}
    SMEDLValue *params_copy = smedl_copy_array(params, {{params_len}});
    if (params_copy == NULL) {
        return 0;
    }
    if (!push_global_event(&queue, CHANNEL_{{conn.channel}}, identities, params_copy, aux)) {
        smedl_free_array(params_copy, {{params_len}});
        return 0;
    }
    return 1;
}
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

int forward_{{syncset}}_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    //TODO identities need to be copied here too since they are external
    {% set params_len = conn.source_event_params|length %}
    SMEDLValue *params_copy = smedl_copy_array(params, {{params_len}});
    if (params_copy == NULL) {
        return 0;
    }
    if (!push_global_event(&queue, CHANNEL_{{conn.channel}}, identities, params_copy, aux)) {
        smedl_free_array(params_copy, {{params_len}});
        return 0;
    }
    return 1;
}
{% endfor %}
