#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include "smedl_types.h"
#include "global_event_queue.h"
#include "{{syncset}}_global_wrapper.h"
{% for decl in mon_decls %}
#include "{{decl.name}}_local_wrapper.h"
{% endfor %}
{% for spec_name in sys.syncset_spec_names(syncset) %}
#include "{{spec_name}}_mon.h"
{% endfor %}

/* Global event queues - containing exported events */
static GlobalEventQueue intra_queue;
static GlobalEventQueue inter_queue;

/* Callback function pointers */
{% for decl in mon_decls %}
{% for conn in decl.inter_connections %}
static SMEDLCallback cb_{{conn.channel}};
{% endfor %}
{% endfor %}

/* Initialization interface - Initialize the global wrapper. Must be called once
 * before importing any events. Return nonzero on success, zero on failure. */
int init_{{syncset}}_syncset() {
    {# No need to initialize intra_queue and inter_queue because they are
        static storage duration (due to being global) thus are initialized to
        NULL automatically #}
    /* Initialize all local wrappers */
    {% for decl in mon_decls %}
    init_{{decl.name}}_local_wrapper();
    {% endfor %}

    return 1;

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
void free_{{syncset}}_syncset() {
    /* Free local wrappers */
    {% for decl in mon_decls %}
    free_{{decl.name}}_local_wrapper();
    {% endfor %}

    /* Unset callbacks */
    {% for decl in mon_decls %}
    {% for conn in decl.inter_connections %}
    cb_{{conn.channel}} = NULL;
    {% endfor %}
    {% endfor %}
}

/* Intra routing function - Called by import interface functions and intra queue
 * processing function to route events to the local wrappers.
 * Return nonzero on success, zero on failure. */
{# Routing function macros ************************************************** #}
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
{% macro free_state_vars(target) %}
{% for var, param in target.state_vars.items() %}
{% if target.monitor.spec.state_vars[var].type is sameas SmedlType.STRING %}
free(init_state.{{var}});
{% elif target.monitor.spec.state_vars[var].type is sameas SmedlType.OPAQUE %}
free(init_state.{{var}}.data);
{% endif %}
{% endfor %}
{% endmacro %}
{# -------------------------------------------------------------------------- #}
{% macro route(conn) -%}
#if DEBUG >= 4
fprintf(stderr, "Global wrapper '{{syncset}}' routing for conn '{{conn.channel}}'\n");
#endif
{% for target in conn.targets if target.monitor in mon_decls -%}
{
    {% if target.mon_params is nonempty %}
    SMEDLValue new_identities[{{target.mon_params|length}}] = {
            {% for param, dest_type in target.mon_params_w_types %}
            {{param_initializer(param, dest_type)|indent(12)}},
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_identities = NULL;
    {% endif %}

    {% if target.target_type == 'creation' %}
    {{target.monitor.spec.name}}State init_state;
    if (!default_{{target.monitor.spec.name}}_state(&init_state)) {
        /* malloc fail */
        return 0;
    }
    {% for var, param in target.state_vars.items() %}
    {% set array_name = "identities" if param.identity else "params" %}
    {% if param.source_type is sameas SmedlType.INT %}
    init_state.{{var}} = {{array_name}}[{{param.index}}].v.i;
    {% elif param.source_type is sameas SmedlType.FLOAT %}
    init_state.{{var}} = {{array_name}}[{{param.index}}].v.d;
    {% elif param.source_type is sameas SmedlType.CHAR %}
    init_state.{{var}} = {{array_name}}[{{param.index}}].v.c;
    {% elif param.source_type is sameas SmedlType.STRING %}
    if (!smedl_replace_string(&init_state.{{var}}, {{array_name}}[{{param.index}}].v.s)) {
        /* malloc fail */
        {{free_state_vars(target)}}return 0;
    }
    {% elif param.source_type is sameas SmedlType.POINTER %}
    init_state.{{var}} = {{array_name}}[{{param.index}}].v.p;
    {% elif param.source_type is sameas SmedlType.THREAD %}
    init_state.{{var}} = {{array_name}}[{{param.index}}].v.th;
    {% elif param.source_type is sameas SmedlType.OPAQUE %}
    if (!smedl_replace_opaque(&init_state.{{var}}, {{array_name}}[{{param.index}}].v.o)) {
        /* malloc fail */
        {{free_state_vars(target)}}return 0;
    }
    {% endif %};
    {% endfor %}

    if (!create_{{target.monitor.name}}(new_identities, &init_state)) {
        /* malloc fail */
        {{free_state_vars(target)}}return 0;
    }
    {% elif target.target_type == 'event' %}
    {% if target.event_params is nonempty %}
    SMEDLValue new_params[{{target.event_params|length}}] = {
            {% for param, dest_type in target.event_params_w_types %}
            {{param_initializer(param, dest_type)|indent(12)}},
            {% endfor %}
        };
    {% else %}
    SMEDLValue *new_params = NULL;
    {% endif %}

    if (!process_{{target.monitor.name}}_{{target.event}}(new_identities, new_params, aux)) {
        /* malloc fail */
        return 0;
    }
    {% endif %}
}
{%- endfor %}
{%- endmacro %}
{# End of routing function macros ******************************************* #}
{% for conn in sys.imported_channels(syncset) %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn)|indent}}
}
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.intra_connections %}
int route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn)|indent}}
}
{% endfor %}
{% endfor %}

/* Intra queue processing function - Route events to the local wrappers. Return
 * nonzero on success, zero on failure. */
static int handle_{{syncset}}_intra() {
    int success = 1;
    int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&intra_queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for decl in mon_decls %}
            {% for conn in decl.intra_connections %}
            case CHANNEL_{{syncset}}_{{conn.channel}}:
                success = success &&
                    route_{{syncset}}_{{conn.channel}}(identities, params, aux);
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
        }

        /* Event params were malloc'd. They are no longer needed. (String and
         * opaque data were already free'd in the switch.) */
        free(params);
    }
    return success;
}

/* Inter queue processing function - Call the export callbacks. Return nonzero
 * on success, zero on failure. */
static int handle_{{syncset}}_inter() {
    int success = 1;
    int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&inter_queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            case CHANNEL_{{syncset}}_{{conn.channel}}:
#if DEBUG >= 4
                fprintf(stderr, "Global wrapper '{{syncset}}' exporting for conn '{{conn.channel}}'\n");
#endif
                if (cb_{{conn.channel}} != NULL) {
                    success = success &&
                        cb_{{conn.channel}}(identities, params, aux);
                }
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
        }

        /* Event params were malloc'd. They are no longer needed. (String and
         * opaque data were already free'd in the switch.) */
        free(params);
    }
    return success;
}

/* Queue processing function - Handle the events in the intra queue, then the
 * inter queue. Return nonzero on success, zero on failure. */
static int handle_{{syncset}}_queues() {
    int success = handle_{{syncset}}_intra();
    return handle_{{syncset}}_inter() && success;
}

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
{% for event, conn in decl.ev_connections.items() %}
int raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% set params_len = decl.spec.exported_events[event]|length %}
    {% if conn in decl.intra_connections %}
    /* Store on intra queue */
    SMEDLValue *params_intra = smedl_copy_array(params, {{params_len}});
    if (!push_global_event(&intra_queue, CHANNEL_{{syncset}}_{{conn.channel}}, identities, params_intra, aux)) {
        /* malloc fail */
        smedl_free_array(params_intra, {{params_len}});
        return 0;
    }
    {% endif %}
    {% if conn in decl.inter_connections %}
    /* Store on inter queue */
    SMEDLValue *params_inter = smedl_copy_array(params, {{params_len}});
    if (!push_global_event(&inter_queue, CHANNEL_{{syncset}}_{{conn.channel}}, identities, params_inter, aux)) {
        /* malloc fail */
        smedl_free_array(params_inter, {{params_len}});
        return 0;
    }
    {% endif %}
}
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

int import_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    int success = route_{{syncset}}_{{conn.channel}}(identities, params, aux);
    return handle_{{syncset}}_queues() && success;
}
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

void callback_{{syncset}}_{{conn.channel}}(SMEDLCallback cb_func) {
    cb_{{conn.channel}} = cb_func;
}
{% endfor %}
{% endfor %}
