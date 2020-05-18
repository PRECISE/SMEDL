#include <stdlib.h>
#include "smedl_types.h"
#include "global_wrapper.h"
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
 * before importing any events. */
void init_{{syncset}}_syncset() {
    /* Initialize all local wrappers */
    {% for decl in mon_decls %}
    init_{{decl.name}}_local_wrapper();
    {% endfor %}
    {# No need to initialize intra_queue and inter_queue because they are
        static storage duration (due to being global) thus are initialized to
        NULL automatically #}
}

/* Cleanup interface - Tear down and free the resources used by this global
 * wrapper and all the local wrappers and monitors it manages. Note that if
 * this is called while there are pending events to be exported (i.e. when a
 * call to any of the import_*() functions has not returned yet), those events
 * will be dropped! */
void free_{{syncset}}_syncset() {
    /* Free local wrappers */
    {% for decl in mon_decls %}
    free_{{decl.name}}_local_wrapper();
    {% endfor %}

    /* Clear queues */
    int mon, event;
    SMEDLValue *identities, *params;
    void *aux;
    while (pop_global_event(&intra_queue, &mon, &identities, &event, &params, &aux)) {
        free(params);
    }
    while (pop_global_event(&inter_queue, &mon, &identities, &event, &params, &aux)) {
        free(params);
    }
}

/* Intra routing function - Called by import interface functions and intra queue
 * processing function to route events to the local wrappers */
{# Routing function macros ************************************************** #}
{% macro param_converter(array_name, param, dest_type) -%}
{% if dest_type is sameas param.source_type %}
{{array_name}}[{{param.index}}]
{%- else %}
{# Numeric types can convert, so we must do that #}
{
    {%- if dest_type is sameas SmedlType.INT %}
    SMEDL_INT, {.i
    {%- elif dest_type is sameas SmedlType.FLOAT %}
    SMEDL_FLOAT, {.d
    {%- elif dest_type is sameas SmedlType.FLOAT %}
    SMEDL_CHAR, {.c
    {%- endif %} = {{array_name}}[{{param.index}}].v.
    {%- if param.source_type is sameas SmedlType.INT %}
    i}
    {%- elif param.source_type is sameas SmedlType.FLOAT %}
    d}
    {%- elif param.source_type is sameas SmedlType.CHAR %}
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
{% macro route(conn) -%}
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
    default_{{target.monitor.spec.name}}_state(&init_state);
    {% for var, param in target.state_vars.items() %}
    init_state.{{var}} = {%+ if param.identity -%}
        identities[{{param.index}}]
        {%- else -%}
        params[{{param.index}}]
        {%- endif -%}
        .v.
        {%- if param.source_type is sameas SmedlType.INT -%}
            i
        {%- elif param.source_type is sameas SmedlType.FLOAT -%}
            d
        {%- elif param.source_type is sameas SmedlType.CHAR -%}
            c
        {%- elif param.source_type is sameas SmedlType.STRING -%}
            s
        {%- elif param.source_type is sameas SmedlType.POINTER -%}
            p
        {%- elif param.source_type is sameas SmedlType.THREAD -%}
            th
        {%- elif param.source_type is sameas SmedlType.OPAQUE -%}
            o
        {%- endif %};
    {% endfor %}

    create_{{target.monitor.name}}_monitor(new_identities, &init_state);
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

    process_{{target.monitor.name}}_{{target.event}}(new_identities, new_params, aux);
    {% endif %}
}
{%- endfor %}
{%- endmacro %}
{# End of routing function macros ******************************************* #}
{% for conn in sys.imported_channels(syncset) %}
void route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn)|indent}}
}
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.intra_connections %}
void route_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{route(conn)|indent}}
}
{% endfor %}
{% endfor %}

/* Intra queue processing function - Route events to the local wrappers */
static void handle_{{syncset}}_intra() {
    unsigned int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&intra_queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for decl in mon_decls %}
            {% for conn in decl.intra_connections %}
            case CHANNEL_{{syncset}}_{{conn.channel}}:
                route_{{syncset}}_{{conn.channel}}(identities, params, aux);
                break;
            {% endfor %}
            {% endfor %}
        }

        /* Event params were malloc'd. They are no longer needed. */
        free(params);
    }
}

/* Inter queue processing function - Call the export callbacks */
static void handle_{{syncset}}_inter() {
    unsigned int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&inter_queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for decl in mon_decls %}
            {% for conn in decl.inter_connections %}
            case CHANNEL_{{syncset}}_{{conn.channel}}:
                cb_{{conn.channel}}(identities, params, aux);
                break;
            {% endfor %}
            {% endfor %}
        }

        /* Event params were malloc'd. They are no longer needed. */
        free(params);
    }
}

/* Queue processing function - Handle the events in the intra queue, then the
 * inter queue */
static void handle_{{syncset}}_queues() {
    handle_{{syncset}}_intra();
    handle_{{syncset}}_inter();
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
{% for event, conn in decl.ev_connections.items() %}
void raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {% set params_len = decl.spec.exported_events[event]|length %}
    {% if conn in decl.intra_connections %}
    /* Store on intra queue */
    SMEDLValue *params_intra = smedl_copy_array(params, {{params_len}});
    if (!push_global_event(&intra_queue, CHANNEL_{{syncset}}_{{conn.channel}}, identities, params_intra, aux)) {
        //TODO Out of memory. What now?
    }
    {% endif %}
    {% if conn in decl.inter_connections %}
    /* Store on inter queue */
    SMEDLValue *params_inter = smedl_copy_array(params, {{params_len}});
    if (!push_global_event(&inter_queue, CHANNEL_{{syncset}}_{{conn.channel}}, identities, params_inter, aux)) {
        //TODO Out of memory. What now?
    }
    {% endif %}
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
{% for conn in sys.imported_channels(syncset) %}

void import_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    route_{{syncset}}_{{conn.channel}}(identities, params, aux);
    handle_{{syncset}}_queues();
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
