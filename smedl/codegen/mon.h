#ifndef {{spec.name}}_MON_H
#define {{spec.name}}_MON_H

#include "smedl_types.h"
#include "event_queue.h"

/* Internal/exported event enum for action queues */
typedef enum {
    {% for event in spec.internal_events.keys() %}
    EVENT_{{spec.name}}_{{event}},
    {% endfor %}
    {% for event in spec.exported_events.keys() %}
    EVENT_{{spec.name}}_{{event}},
    {% endfor %}
} {{spec.name}}Event;

/* Scenario state enums */
{% for scenario in spec.scenarios %}
typedef enum {
    {% if scenario.implicit_states > 0 %}
    /* Explicit states */
    {% endif %}
    {% for state in scenario.states %}
    STATE_{{spec.name}}_{{scenario.name}}_{{state}},
    {% endfor %}
    {% if scenario.implicit_states > 0 %}
    /* Implicit states */
    {% for i in range(scenario.implicit_states) %}
    STATE_{{spec.name}}_{{scenario.name}}_{{i}},
    {% endfor %}
    {% endif %}
} {{spec.name}}_{{scenario.name}}_State;
{% endfor %}

/* State variables for {{spec.name}}.
 * Used for initialization as well as in the {{spec.name}}Monitor
 * struct. */
typedef struct {{spec.name}}State {
    {% for var in spec.state_vars.values() %}
    {{var.type.c_type}} {{var.name}};
    {% endfor %}
} {{spec.name}}State;

/* {{spec.name}} monitor struct.
 * Maintains all of the internal state for the monitor. */
typedef struct {{spec.name}}Monitor {
    /* Array of monitor's identities */
    SMEDLValue *identities;

    /* Scenario states */
    {% for scenario in spec.scenarios %}
    {{spec.name}}_{{scenario.name}}_State {{scenario.name}}_state;
    {% endfor %}

    /* Scenario execution flags (ensures each scenario only processes one event
     * per macro-step) */
    struct {
        {% for scenario in spec.scenarios %}
        unsigned int {{scenario.name}}_flag : 1;
        {% endfor %}
    } ef;

    /* State variables */
    {{spec.name}}State s;

    /* Exported event callback pointers */
    {% for event in spec.exported_events.keys() %}
    SMEDLCallback callback_{{event}};
    {% endfor %}

    /* Local event queue */
    EventQueue event_queue;

    //TODO mutex?
} {{spec.name}}Monitor;

/* Callback registration functions - Set the export callback for an exported
 * event. Set to NULL to unregister a callback. */
{% for event in spec.exported_events.keys() %}
void register_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLCallback cb_func);
{% endfor %}

/* Event handling functions:
 *
 * execute_* - For imported and internal events, process the event through the
 *   scenarios. For exported events, do that and then export by calling the
 *   callback. This is the function to call to "import" an imported event.
 * queue_* - Queue an internal or exported event for processing. ("Raise" the
 *   event.) Note that for exported events, this refers to internal queuing
 *   within the monitor. If the monitor belongs to a synchronous set, the global
 *   wrapper's queuing happens when the event is actually exported.
 * export_* - Export an exported event by calling the registered callback, if
 *   any. */
{% for event in spec.imported_events.keys() %}
void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
{% endfor %}
{% for event in spec.internal_events.keys() %}
void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
void queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
{% endfor %}
{% for event in spec.exported_events.keys() %}
void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
void queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
void export_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux);
{% endfor %}

/* Monitor management functions */

/* Initialize a {{spec.name}} monitor with default state.
 * Return a pointer to the monitor. Must be freed with
 * free_{{spec.name}}_monitor() when no longer needed. */
{{spec.name}}Monitor * init_{{spec.name}}_monitor(SMEDLValue *identities);

/* Fill the provided {{spec.name}}State
 * with the default initial values for the monitor. Note that strings and
 * opaque data must be free()'d if they are reassigned! The following two
 * functions from smedl_types.h make that simple:
 * - smedl_replace_string()
 * - smedl_replace_opaque() */
void default_{{spec.name}}_state({{spec.name}}State *state);

/* Initialize a {{spec.name}} monitor with the provided state.
 * Return a pointer to the monitor. Must be freed with
 * free_{{spec.name}}_monitor() when no longer needed. */
{{spec.name}}Monitor * init_{{spec.name}}_with_state(SMEDLValue *identities, {{spec.name}}State *init_state);

/* Free a {{spec.name}} monitor. NOTE: Does not free the identities. That must
 * be done by the caller, if necessary. */
void free_{{spec.name}}_monitor({{spec.name}}Monitor *mon);

#endif /* {{spec.name}}_MON_H */
