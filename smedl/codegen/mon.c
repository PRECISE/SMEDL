#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include <string.h>
#include "smedl_types.h"
#include "event_queue.h"
#include "{{spec.name}}_mon.h"
{% if spec.helpers is nonempty %}

/* Helper includes */
{% for include in spec.helpers %}
#include {{include}}
{% endfor %}
{% endif %}

/* Callback registration functions - Set the export callback for an exported
 * event */
{% for event in spec.exported_events.keys() %}

void register_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLCallback cb_func) {
    mon->callback_{{event}} = cb_func;
}
{% endfor %}

/* Cleanup callback registration function - Set the callback for when the
 * monitor is ready to be recycled. The callback is responsible for calling
 * free_{{spec.name}}_monitor(). */
void registercleanup_{{spec.name}}({{spec.name}}Monitor *mon, int (*cleanup_func)({{spec.name}}Monitor *mon)) {
    mon->cleanup = cleanup_func;
}
{% if spec.get_final_states() is nonempty %}

/* Check if all final states have been reached, and if so, call the cleanup
 * callback (if registered) */
static int check_final_states({{spec.name}}Monitor *mon) {
    if ({% for scenario, state in spec.get_final_states().items() -%}
        mon->{{scenario}}_state == STATE_{{spec.name}}_{{scenario}}_{{state}}{% if not loop.last %} &&
        {% endif %}{% endfor %}) {
        if (mon->cleanup != NULL) {
            return mon->cleanup(mon);
        }
    }
    return 1;
}
{% endif %}

/* Queue processing function - Call the handlers for all the events in the
 * queue until it is empty.
 * Return nonzero if all handlers ran successfully, zero if not. */
static int handle_{{spec.name}}_queue({{spec.name}}Monitor *mon) {
    int success = 1;
    int event;
    SMEDLValue *params;
    void *aux;

    while (pop_event(&mon->event_queue, &event, &params, &aux)) {
        switch (event) {
            {% for event, params in chain(spec.internal_events.items(),
                   spec.exported_events.items()) %}
            case EVENT_{{spec.name}}_{{event}}:
                success = success &&
                    execute_{{spec.name}}_{{event}}(mon, params, aux);
                {% for param_type in params %}
                {% if param_type is sameas SmedlType.STRING %}
                free(params[{{loop.index0}}].v.s);
                {% elif param_type is sameas SmedlType.OPAQUE %}
                free(params[{{loop.index0}}].v.o.data);
                {% endif %}
                {% endfor %}
                break;
            {% endfor %}
        }

        free(params);
    }

    /* Macro-step is finished. */
    memset(&mon->ef, 0, sizeof(mon->ef));
{% if spec.get_final_states() is nonempty %}
    success = check_final_states(mon) && success;
{% endif %}
    return success;
}

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
 *   any.
 *
 * All return nonzero on success, zero on failure. Note that when an event
 * handler fails, it means the monitor is no longer consistent with its
 * specification, has very possibly dropped events, and is likely to misbehave
 * when handling future events. However, it is still safe to clean it up, and
 * it will not leak memory as long as that is done.
 * TODO When could future events actually cause crashes? I suspect it's
 * possible when there are strings or opaques and helper functions, but not
 * otherwise. */
{# Event handler macros ***************************************************** #}
{% macro expression(e) -%}
{% if e.parens %}({% endif -%}
{% if e.expr_type == 'state_var' %}
mon->s.{{e.name}}
{%- elif e.expr_type == 'param' %}
params[{{e.idx}}].v.
    {%- if e.type is sameas SmedlType.INT -%}
        i
    {%- elif e.type is sameas SmedlType.FLOAT -%}
        d
    {%- elif e.type is sameas SmedlType.CHAR -%}
        c
    {%- elif e.type is sameas SmedlType.STRING -%}
        s
    {%- elif e.type is sameas SmedlType.POINTER -%}
        p
    {%- elif e.type is sameas SmedlType.THREAD -%}
        th
    {%- elif e.type is sameas SmedlType.OPAQUE -%}
        o
    {%- endif %}
{%- elif e.expr_type == 'literal' %}
{{e.string}}
{%- elif e.expr_type == 'helper_call' %}
{{e.name}}(
    {%- for param in e.params -%}
        {{expression(param)}}
        {%- if not loop.last %}, {%+ endif -%}
    {%- endfor -%}
    )
{%- elif e.expr_type == 'unary_op' %}
{{e.operator}}{{expression(e.operand)}}
{%- elif e.expr_type == 'binary_op' %}
{# == or != on strings and opaques requires special handling. #}
{% if e.operator == '==' and
        (e.left.type is sameas SmedlType.STRING or
        e.right.type is sameas SmedlType.STRING) %}
!strcmp({{expression(e.left)}}, {{expression(e.right)}})
{%- elif e.operator == '!=' and
        (e.left.type is sameas SmedlType.STRING or
        e.right.type is sameas SmedlType.STRING) %}
strcmp({{expression(e.left)}}, {{expression(e.right)}})
{%- elif e.operator == '==' and
        (e.left.type is sameas SmedlType.OPAQUE or
        e.right.type is sameas SmedlType.OPAQUE) %}
smedl_opaque_equals({{expression(e.left)}}, {{expression(e.right)}})
{%- elif e.operator == '!=' and
        (e.left.type is sameas SmedlType.OPAQUE or
        e.right.type is sameas SmedlType.OPAQUE) %}
!smedl_opaque_equals({{expression(e.left)}}, {{expression(e.right)}})
{%- else %}
{{expression(e.left)}} {{e.operator}} {{expression(e.right)}}
{%- endif %}
{% endif %}
{%- if e.parens -%}){%- endif -%}
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% macro action(a) -%}
{% if a.action_type == 'assignment' %}
{# String and opaque state vars must be free'd and malloc'd when reassigned. See
    issues #37 and #48 #}
{% if spec.state_vars[a.var].type is sameas SmedlType.STRING %}
if (!smedl_replace_string(&mon->s.{{a.var}}, {{expression(a.expr)}})) {
    /* malloc fail */
    return 0;
}
{%- elif spec.state_vars[a.var].type is sameas SmedlType.STRING %}
if (!smedl_replace_opaque(&mon->s.{{a.var}}, {{expression(a.expr)}})) {
    /* malloc fail */
    return 0;
}
{%- else %}
mon->s.{{a.var}} = {{expression(a.expr)}};
{%- endif %}
{% elif a.action_type == 'increment' %}
mon->s.{{a.var}}++;
{%- elif a.action_type == 'decrement' %}
mon->s.{{a.var}}--;
{%- elif a.action_type == 'raise' %}
{
    {# This is freed in handle_{{spec.name}}_queue() #}
    SMEDLValue *new_params = malloc(sizeof(SMEDLValue) * {{spec.get_event(a.event)|length}});
    if (new_params == NULL) {
        /* malloc fail */
        return 0;
    }
    {% for param_type in spec.get_event(a.event) %}
    new_params[{{loop.index0}}].t = SMEDL_{{param_type.value|upper}};
    {% if param_type is sameas SmedlType.INT %}
    new_params[{{loop.index0}}].v.i = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.FLOAT %}
    new_params[{{loop.index0}}].v.d = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.CHAR %}
    new_params[{{loop.index0}}].v.c = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.STRING %}
    if (!smedl_assign_string(&new_params[{{loop.index0}}].v.s, {{expression(a.params[loop.index0])}})) {
        /* malloc fail */
        smedl_free_array(new_params, {{loop.index0}});
        return 0;
    }
    {% elif param_type is sameas SmedlType.POINTER %}
    new_params[{{loop.index0}}].v.p = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.THREAD %}
    new_params[{{loop.index0}}].v.th = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.OPAQUE %}
    if (!smedl_assign_opaque(&new_params[{{loop.index0}}].v.o, {{expression(a.params[loop.index0])}})) {
        /* malloc fail */
        smedl_free_array(new_params, {{loop.index0}});
        return 0;
    }
    {% endif %}
    {% endfor %}
    queue_{{spec.name}}_{{a.event}}(mon, new_params, aux);
}
{%- elif a.action_type == 'call' %}
{{a.function}}(
    {%- for param in a.params -%}
    {{expression(param)}}
        {%- if not loop.last %}, {%+ endif -%}
    {%- endfor -%}
    );

{%- endif %}
{%- endmacro %}
{# -------------------------------------------------------------------------- #}
{% macro event_handler(event) -%}
{% for scenario in spec.scenarios if scenario.handles_event(event) %}
/* {{scenario.name}} scenario */
//if (!mon->ef.{{scenario.name}}_flag) {
    switch (mon->{{scenario.name}}_state) {
        {% for state in scenario.all_states if (state, event) in scenario.steps %}
        case STATE_{{spec.name}}_{{scenario.name}}_{{state}}:
            {# Note: We don't try to do anything special if the condition is 1
                (like disable the "else" and further "else if"s) because it
                would complicate the template and the compiler should optimize
                this for us anyway. #}
            {% for condition, dest, actions in scenario.steps[(state, event)] %}
            {%+ if not loop.first %}} else {%+ endif %}if ({{expression(condition)}}) {
                {% for a in actions %}
                {{action(a)|indent(16)}}
                {% endfor %}

                mon->{{scenario.name}}_state = STATE_{{spec.name}}_{{scenario.name}}_{{dest}};
            {% endfor %}
            } else {
                {% if (state, event) in scenario.elses %}
                {% for a in scenario.elses[(state, event)][1] %}
                {{action(a)|indent(16)}}
                {% endfor %}

                mon->{{scenario.name}}_state = STATE_{{spec.name}}_{{scenario.name}}_{{scenario.elses[(state, event)][0]}};
                {% else %}
                /* XXX Do something here: Event matches but conditions
                 * not met, no else */
                {% endif %}
            }
            break;

        {% endfor %}
        default:
            /* XXX Do something here: Scenario handles this event but not
             * from this state */
            ;
    }
    //mon->ef.{{scenario.name}}_flag = 1;
//}
{%- if not loop.last %}


{% endif %}
{% endfor %}
{%- endmacro %}
{# End of event handler macros ********************************************** #}
{% if spec.imported_events is nonempty %}

/* Imported events */
{% for event in spec.imported_events.keys() %}

int execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Monitor '{{spec.name}}' handling imported event '{{event}}'\n");
#endif

    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}

    {% endif %}
    /* Finish the macro-step */
    return handle_{{spec.name}}_queue(mon);
}
{% endfor %}
{% endif %}
{% if spec.internal_events is nonempty %}

/* Internal events */
{% for event in spec.internal_events.keys() %}

int execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Monitor '{{spec.name}}' handling internal event '{{event}}'\n");
#endif

    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}
    {% endif %}

    return 1;
}

int queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Monitor '{{spec.name}}' queuing raised internal event '{{event}}'\n");
#endif

    return push_event(&mon->event_queue, EVENT_{{spec.name}}_{{event}}, params, aux);
}
{% endfor %}
{% endif %}
{% if spec.exported_events is nonempty %}

/* Exported events */
{% for event in spec.exported_events.keys() %}

int execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Monitor '{{spec.name}}' handling exported event '{{event}}'\n");
#endif

    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}

    {% endif %}
    /* Export the event */
    return export_{{spec.name}}_{{event}}(mon, params, aux);
}

int queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Monitor '{{spec.name}}' queuing raised exported event '{{event}}'\n");
#endif

    return push_event(&mon->event_queue, EVENT_{{spec.name}}_{{event}}, params, aux);
}

int export_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    if (mon->callback_{{event}} != NULL) {
        return (mon->callback_{{event}})(mon->identities, params, aux);
    }
    return 1;
}
{% endfor %}
{% endif %}

/* Monitor management functions */

/* Initialize a {{spec.name}} monitor with default state.
 * Return a pointer to the monitor. Must be freed with
 * free_{{spec.name}}_monitor() when no longer needed.
 * Returns NULL on malloc failure. */
{{spec.name}}Monitor * init_{{spec.name}}_monitor(SMEDLValue *identities) {
    {{spec.name}}State init_state;

    /* Initialize the monitor with default state */
    if (!default_{{spec.name}}_state(&init_state)) {
        /* malloc fail */
        return NULL;
    }
    {{spec.name}}Monitor *result = init_{{spec.name}}_with_state(identities, &init_state);
    if (result == NULL) {
        /* malloc fail. Need to clean up strings and opaques in init_state. */
        {% for var in spec.state_vars.values() %}
        {% if var.type is sameas SmedlType.STRING %}
        free(init_state.{{var.name}});
        {% elif var.type is sameas SmedlType.OPAQUE %}
        free(init_state.{{var.name}}.data);
        {% endif %}
        {% endfor %}
    }
    return result;
}

{% macro free_state_vars(idx) %}
{# Free string and opaque state variables that have already been allocated #}
{% for var in (spec.state_vars.values()|list)[:idx] %}
{% if var.type is sameas SmedlType.STRING %}
free(state->{{var.name}});
{% elif var.type is sameas SmedlType.OPAQUE %}
free(state->{{var.name}}.data);
{% endif %}
{% endfor %}
{% endmacro %}
/* Fill the provided {{spec.name}}State
 * with the default initial values for the monitor. Note that strings and
 * opaque data must be free()'d if they are reassigned! The following two
 * functions from smedl_types.h make that simple:
 * - smedl_replace_string()
 * - smedl_replace_opaque()
 * Returns nonzero on success, zero on malloc failure. */
int default_{{spec.name}}_state({{spec.name}}State *state) {
    {% for var in spec.state_vars.values() %}
    {% if var.initial_value is not none %}
    {# Strings and opaques must be malloc'd because when they are reassigned,
        the old value is free'd and the new value malloc'd again. See issue
        #48 #}
    {% if var.type is sameas SmedlType.STRING %}
    if (!smedl_assign_string(&state->{{var.name}}, {{var.initial_value}})) {
        /* Out of memory */
        {{free_state_vars(loop.index0)|indent(8)}}return 0;
    }
    {% elif var.type is sameas SmedlType.OPAQUE %}
    if (!smedl_assign_opaque(&state->{{var.name}}, {{var.initial_value}})) {
        /* Out of memory */
        {{free_state_vars(loop.index0)|indent(8)}}return 0;
    }
    {% else %}
    state->{{var.name}} = {{var.initial_value}};
    {% endif %}
    {% endif %}
    {% endfor %}
    return 1;
}

/* Initialize a {{spec.name}} monitor with the provided state. Note that this
 * function takes ownership of the memory used by any strings and opaques when
 * successful! (That is, it will call free() on them when they are no longer
 * needed.) default_{{spec.name}}_state() is aware of this, so unless changing
 * initial string or opaque state, there is no need to be concerned about this.
 *
 * Return a pointer to the monitor. Must be freed with
 * free_{{spec.name}}_monitor() when no longer needed.
 * Returns NULL on malloc failure. */
{{spec.name}}Monitor * init_{{spec.name}}_with_state(SMEDLValue *identities, {{spec.name}}State *init_state) {
    {{spec.name}}Monitor *mon = malloc(sizeof({{spec.name}}Monitor));
    if (mon == NULL) {
        return NULL;
    }

    /* Store the assigned identities */
    mon->identities = identities;

    /* Copy initial state vars in */
    mon->s = *init_state;

    /* Set all scenarios to their initial state */
    {% for scenario in spec.scenarios %}
    mon->{{scenario.name}}_state = 0;
    {% endfor %}

    /* Reset all scenario execution flags */
    memset(&mon->ef, 0, sizeof(mon->ef));

    /* Set all export callbacks to NULL */
    {% for event in spec.exported_events.keys() %}
    mon->callback_{{event}} = NULL;
    {% endfor %}

    /* Initialize event queue */
    mon->event_queue = (EventQueue){0};

    return mon;
}

/* Free a {{spec.name}} monitor */
void free_{{spec.name}}_monitor({{spec.name}}Monitor *mon) {
    {% for var in spec.state_vars.values() %}
    {% if var.type is sameas SmedlType.STRING %}
    free(mon->s.{{var.name}});
    {% elif var.type is sameas SmedlType.OPAQUE %}
    free(mon->s.{{var.name}}.data);
    {% endif %}
    {% endfor %}
    free(mon);
}
