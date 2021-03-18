{% if pure_async %}
#include <stdio.h>
{% else %}
#if DEBUG > 0
#include <stdio.h>
#endif
{% endif %}
#include <stdlib.h>
#include "smedl_types.h"
#include "global_event_queue.h"
#include "{{sys.name}}_defs.h"
#include "{{syncset}}_global_wrapper.h"
#include "{{syncset}}_{{sys.transport}}.h"
#include "{{syncset}}_manager.h"
{% if pure_async %}
#include <signal.h>

/* Set to 1 to initiate clean shutdown. */
volatile sig_atomic_t smedl_interrupted = 0;
{% endif %}

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
    if (!init_{{sys.transport}}()) {
        free_{{syncset}}_syncset();
        return 0;
    }
    return 1;
}

/* Cleanup interface - Tear down and free resources used by the manager and the
 * global wrapper and network interfaces attached to it. */
void free_manager(void) {
    free_{{sys.transport}}();
    free_{{syncset}}_syncset();
}

{% if pure_async %}
/* Run interface - This is a pure asynchronous manager (no PEDL events are
 * attached synchronously). Run until the program is interrupted with SIGINT
 * or SIGTERM (or smedl_interrupted is set to nonzero, the action taken by
 * the handlers for these signals).
 *
 * Returns nonzero on success and zero on failure. */
{% else %}
/* Run interface - Process all pending events in all attached synchronous sets
 * and network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
{% endif %}
int run_manager(void) {
    int result = 1;

    {% if pure_async %}
    while (!smedl_interrupted) {
        if (!run_{{sys.transport}}(1)) {
            fprintf(stderr, "Error while running network endpoint\n");
            result = 0;
        }

        if (!process_queue()) {
            fprintf(stderr, "Error while processing manager queue\n");
            result = 0;
        }
    }
    {% else %}
    // First, run syncset wrapper to process events from the target program.
    result = run_{{syncset}}() && result;

    //TODO When adding threading support, network can run in separate thread.
    // run_{{sys.transport}}() call and loop not necessary, just a single
    // process_queue().
    do {
        result = process_queue() && result;
        result = run_{{sys.transport}}(0) && result;
    } while (queue.head != NULL);
    {% endif %}

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
        free(identities);
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
{% else %}
SMEDLValue *ids_copy = NULL;
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
    return forward_{{sys.transport}}_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux);
}
{% endfor %}
{% if pure_async %}

/* Signal handler for SIGINT and SIGTERM to shutdown gracefully. Sets the
 * interrupted flag to 1. */
static void set_interrupted(int signum) {
    /* Windows and some other platforms reset the signal handler to the default
     * when a signal is received. Set it back to this function. This creates a
     * race condition on these platforms, but more reliable functions are not
     * cross platform (not that all platforms handle signal() the same way
     * either, or even use SIGINT and SIGTERM at all, but at least they are
     * standard C). Anyway, the worst case scenario is two SIGINT/SIGTERM
     * arrive back to back, the second arrives before the signal handler is
     * set back to this function, and the program is terminated immediately
     * instead of shutting down cleanly. The only thing lost is notifying the
     * server of our exit so it can clean up before it notices we died. */
    signal(signum, set_interrupted);
    smedl_interrupted = 1;
}

int {% if cpp %}c_{% endif %}main(int argc, char **argv) {
    // Set signal handlers so we can shut down cleanly
    if (signal(SIGINT, set_interrupted) == SIG_ERR) {
        fprintf(stderr, "Could not set SIGINT handler\n");
        return 2;
    }
    if (signal(SIGTERM, set_interrupted) == SIG_ERR) {
        fprintf(stderr, "Could not set SIGTERM handler\n");
        return 2;
    }

    if (!init_manager()) {
        return 1;
    }

    int result = run_manager();
    free_manager();

    if (result) {
        return 0;
    } else {
        return 1;
    }
}

{% endif %}
