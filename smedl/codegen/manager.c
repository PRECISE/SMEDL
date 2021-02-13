#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include "smedl_types.h"
#include "global_event_queue.h"
#include "{{sys.name}}_defs.h"
#include "{{syncset}}_global_wrapper.h"
#include "{{syncset}}_async.h"
#include "{{syncset}}_manager.h"

/* Manager event queue */
static GlobalEventQueue queue;

/* Initialization interface - Initialize the manager and the attached global
 * wrapper and network interfaces.
 *
 * Returns nonzero on success, zero on failure. */
int init_manager(void) {
    if (!init_{{syncset}}_syncset()) {
        return 0;
    }
    if (!init_async(0)) {
        free_{{syncset}}_syncset();
        return 0;
    }
    return 1;
}

/* Cleanup interface - Tear down and free resources used by the manager and the
 * global wrapper and network interfaces attached to it. */
void free_manager(void) {
    free_async();
    free_{{syncset}}_syncset();
}

/* Run interface - Process all pending events in all attached synchronous sets
 * and network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
int run_manager(void) {
    int result = 1;

    // First, run syncset wrapper to process events from the target program.
    result = run_{{syncset}}() && result;

    //TODO When adding threading support, network can run in separate thread.
    // run_async() call and loop not necessary, just a single process_queue().
    do {
        result = process_queue() && result;
        result = run_async() && result;
    } while (queue->head != NULL);

    return result;
}

/* Queue processing function - Deliver the events in the manager queue to their
 * destinations.
 *
 * Returns nonzero on success and zero on failure. */
int process_queue(void) {
    int success = 1;
    int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for conn in sys.imported_channels(syncset) %}
            case CHANNEL_{{conn.channel}}:
                success = deliver_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux) && success;
                {% if conn.source_mon is not none %}
                {% for param_type in conn.source_mon.params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(identites[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(identites[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                {% endif %}
                {% for param_type in conn.source_event_params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(params[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(params[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                break;
            {% endfor %}
            {% for conn in sys.exported_channels(syncset).keys() %}
            case CHANNEL_{{conn.channel}}:
                success = deliver_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux) && success;
                {% if conn.source_mon is not none %}
                {% for param_type in conn.source_mon.params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(identites[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(identites[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                {% endif %}
                {% for param_type in conn.source_event_params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(params[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(params[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                break;
            {% endfor %}
        }

        /* Ids and event params were malloc'd. They are no longer needed.
         * (String and opaque data were already free'd in the switch.) */
        free(params);
    }
    return success;
}

/* Manager queueing interfaces - Queue events to be forwarded to monitors or
 * network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
{# -------------------------------------------------------------------------- #}
{% macro enqueue(conn) -%}
{% if conn.source_mon is not none %}
{% set ids_len = conn.source_mon.params|length %}
SMEDLValue *ids_copy = smedl_copy_array(identities, {{ids_len}});
if (ids_copy == NULL) {
    return 0;
}
{% endif %}
{% set params_len = conn.source_event_params|length %}
SMEDLValue *params_copy = smedl_copy_array(params, {{params_len}});
if (params_copy == NULL) {
    {% if conn.source_mon is not none %}
    smedl_free_array(ids_copy, {{ids_len}});
    {% endif %}
    return 0;
}
if (!push_global_event(&queue, CHANNEL_{{conn.channel}}, ids_copy, params_copy, aux)) {
    smedl_free_array(params_copy, {{params_len}});
    {% if conn.source_mon is not none %}
    smedl_free_array(ids_copy, {{ids_len}});
    {% endif %}
    return 0;
}
return 1;
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% for conn in sys.imported_channels(syncset) %}

int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{enqueue(conn)|indent}}
}
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}

int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    {{enqueue(conn)|indent}}
}
{% endfor %}

/* Manager routing functions - One for each event entering or leaving the
 * synchronous set. Called to route each event from the queue appropriately to
 * the global wrapper or network interfaces.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.imported_channels(syncset) %}

int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    if (forward_{{syncset}}_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux)) {
        return run_{{syncset}}();
    }
    return 0;
}
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}

int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    return forward_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux);
}
{% endfor %}
