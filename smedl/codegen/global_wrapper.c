#include "smedl_types.h"
#include "global_wrapper.h"
#include "{{syncset}}_global_wrapper.h"
{% for decl in mon_decls %}
#include "{{decl.name}}_local_wrapper.h"
{% endfor %}
{% for spec_name in sys.get_syncset_spec_names(syncset) %}
#include "{{spec_name}}_mon.h"
{% endfor %}

/* Global event queues - containing exported events */
static GlobalEventQueue intra_queue;
static GlobalEventQueue inter_queue;

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
    SMEDLAux aux;
    while (pop_global_event(&intra_queue, &mon, &identities, &event, &params, &aux)) {
        free(params);
    }
    while (pop_global_event(&inter_queue, &mon, &identities, &event, &params, &aux)) {
        free(params);
    }
}

/* Intra queue processing function - Route events to the local wrappers */
static void handle_{{syncset}}_intra() {
    int mon, event;
    SMEDLValue *identities, *params;
    SMEDLAux aux;

    while (pop_global_event(&intra_queue, &mon, &identities, &event, &params, &aux)) {
        switch (mon) {
            {% for decl in mon_decls
                if decl.has_intra_events(sys.syncsets[syncset]) %}
            case MONITOR_{{syncset}}_{{decl.name}}:
                switch (event) {
                    {% for event, params in decl.spec.exported_events.items()
                       if decl.is_event_intra(event, sys.syncsets[syncset]) %}
                    case EVENT_{{decl.spec.name}}_{{event}}:
                    {% for target in decl.connections[event]
                        if target.monitor in sys.syncsets[syncset] %}
                    {
                        {% if target.mon_params is nonempty %}
                        SMEDLValue new_identities[{{target.mon_params|length}}] = {
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
                            {% set param_type = decl.params[param.index] %}
                            {%- else -%}
                            params[{{param.index}}]
                            {% set param_type = params[param.index] %}
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
                        SMEDLValue new_params[{{target.event_params|length}}] = {
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
                    }
                    {% endfor %}
                        break;
                    {% endfor %}
                }
                break;
            {% endfor %}
        }

        /* Event params were malloc'd. They are no longer needed. */
        free(params);
    }
}

/* Inter queue processing function - Call the export callbacks */
static void handle_{{syncset}}_inter() {
    int mon, event;
    SMEDLValue *identities, *params;
    SMEDLAux aux;

    while (pop_global_event(&inter_queue, &mon, &identities, &event, &params, &aux)) {
        switch (mon) {
            {% for decl in mon_decls
                if decl.has_inter_events(sys.syncsets[syncset]) %}
            case MONITOR_{{syncset}}_{{decl.name}}:
                switch (event) {
                    {% for event, params in decl.spec.exported_events.items()
                       if decl.is_event_inter(event, sys.syncsets[syncset]) %}
                    case EVENT_{{decl.spec.name}}_{{event}}:
                    {% for target in decl.connections[event]
                        if target.monitor not in sys.syncsets[syncset] %}
                        cb_{{target.channel}}(identities, params, aux);
                    {% endfor %}
                        break;
                    {% endfor %}
                }
                break;
            {% endfor %}
        }
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
{% for event, params in decl.spec.exported_events.items() %}

void raise_{{decl.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    {% if decl.is_event_intra(event, sys.syncsets[syncset]) %}
    /* Store on intra queue */
    SMEDLValue *params_intra = smedl_copy_array(params, {{params|length}});
    if (!push_global_event(&intra_queue, MONITOR_{{syncset}}_{{decl.name}}, identities, EVENT_{{decl.spec.name}}_{{event}}, params_intra, aux)) {
        //TODO Out of memory. What now?
    }
    {% if decl.is_event_inter(event, sys.syncsets[syncset]) %}

    {% endif %}
    {% endif %}
    {% if decl.is_event_inter(event, sys.syncsets[syncset]) %}
    /* Store on inter queue */
    SMEDLValue *params_inter = smedl_copy_array(params, {{params|length}});
    if (!push_global_event(&inter_queue, MONITOR_{{syncset}}_{{decl.name}}, identities, EVENT_{{decl.spec.name}}_{{event}}, params_inter, aux)) {
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
{% macro import_handler(target) %}
    {% if target.mon_params is nonempty %}
    SMEDLValue new_identities[{{target.mon_params|length}}] = {
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
    {% set param_type =
        sys.monitor_decls[target.monitor].spec.state_vars[var].type %}
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
    SMEDLValue new_params[{{target.event_params|length}}] = {
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
{% for target_list in sys.imported_connections.values() %}
{% for target in target_list if target.monitor in sys.syncsets[syncset] %}

void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    {{import_handler(target)}}

    handle_{{syncset}}_queues();
}
{% endfor %}
{% endfor %}
{# Events from other synchronous sets #}
{% for decl in sys.monitor_decls.values() if decl.syncset != syncset %}
{% for target_list in decl.connections.values() %}
{% for target in target_list if target.monitor in sys.syncsets[syncset] %}

void import_{{syncset}}_{{target.channel}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    {{import_handler(target)}}

    handle_{{syncset}}_queues();
}
{% endfor %}
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
