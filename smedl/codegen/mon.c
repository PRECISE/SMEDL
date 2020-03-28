#include "smedl_types.h"
#include "events.h" //TODO Move Event to a monitor.h and GlobalEvent to a
                     // wrapper.h?
{% if spec.helpers is nonempty %}

/* Helper includes */
{% for include in spec.helpers %}
#include {{include}}
{% endfor %}
{% endif %}

/* Scenario state enums */
{% for scenario in spec.scenarios %}
typedef enum {
    {% for state in scenario.states %}
    STATE_{{spec.name}}_{{scenario.name}}_{{state}},
    {% endfor %}
} {{spec.name}}_{{scenario.name}}_State;
{% endfor %}

/* Internal/exported event enum for action queues */
typedef enum {
    {% for 
} {{spec.name}}_Event;

typedef struct {{spec.name}Monitor {
    /* Pointer to array of monitor's identities */
    SMEDLValue **identities;

    //TODO Local wrapper should set these to the global wrapper export functions
    // when initializing the monitor
    /* Exported event callback pointers */
    {% for ev, params in spec.exported_events.items() %}
    void (*callback_{{spec.name}}_{{ev}})(SMEDLValue *identities, SMEDLValue *params, Aux aux);
    {% endfor %}

    /* Scenario states */
    {% for scenario in spec.scenarios %}
    {{spec.name}}_{{scenario.name}}_State {{scenario.name}}_state;
    {% endfor %}

    /* State variables */
    {% for var in spec.state_vars %}
    {{var.type.c_type}} {{var.name}}_var;
    {% endfor %}

    /* Local event queue */
    Event *event_queue;

    //TODO mutex?
}

/* Monitor management functions */
//TODO

/* Event handling functions:
 *
 * execute_* - For imported and internal events, process the event through the
 *   scenarios. For exported events, do the export by calling the callback. This
 *   is the function to call to "import" an imported event.
 * queue_* - Queue an internal event for processing or exported event for
 *   export.
 * callback_* - Set the export callback for an exported event */
/* TODO Use array of SMEDLValue to pass all parameters */
{% for event in spec.imported_events.keys() %}
void execute_{{spec.name}}_{{event}}(/* TODO */);
{% endfor %}
{% for event in spec.internal_events.keys() %}
void execute_{{spec.name}}_{{event}}(/* TODO */);
void queue_{{spec.name}}_{{event}}(/* TODO */);
{% endfor %}
{% for event in spec.exported_events.keys() %}
void execute_{{spec.name}}_{{event}}(/* TODO */);
void queue_{{spec.name}}_{{event}}(/* TODO */);
void callback_{{spec.name}}_{{event}}(/* TODO */);
{% endfor %}
