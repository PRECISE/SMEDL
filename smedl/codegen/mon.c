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

/* Queue processing function - Call the handlers for all the events in the
 * queue until it is empty */
static void handle_{{spec.name}}_queue({{spec.name}}Monitor *mon) {
    int event;
    SMEDLValue *params;
    void *aux;

    while (pop_event(&mon->event_queue, &event, &params, &aux)) {
        switch (event) {
            {% for event, params in chain(spec.internal_events.items(),
                   spec.exported_events.items()) %}
            case EVENT_{{spec.name}}_{{event}}:
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

    /* Macro-step is finished. Reset the scenario execution flags. */
    memset(&mon->ef, 0, sizeof(mon->ef));
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
 *   any. */
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
opaque_equals({{expression(e.left)}}, {{expression(e.right)}})
{%- elif e.operator == '!=' and
        (e.left.type is sameas SmedlType.OPAQUE or
        e.right.type is sameas SmedlType.OPAQUE) %}
!opaque_equals({{expression(e.left)}}, {{expression(e.right)}})
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
    /* TODO What to do if malloc fails? */
}
{%- elif spec.state_vars[a.var].type is sameas SmedlType.STRING %}
if (!smedl_replace_opaque(&mon->s.{{a.var}}, {{expression(a.expr)}})) {
    /* TODO What to do if malloc fails? */
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
        /* TODO What to do if malloc fails? */
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
        //TODO Need to malloc a copy and later free
    if (!smedl_assign_string(&new_params[{{loop.index0}}].v.s, {{expression(a.params[loop.index0])}})) {
        /* TODO What to do if malloc fails? */
    }
    {% elif param_type is sameas SmedlType.POINTER %}
    new_params[{{loop.index0}}].v.p = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.THREAD %}
    new_params[{{loop.index0}}].v.th = {{expression(a.params[loop.index0])}};
    {% elif param_type is sameas SmedlType.OPAQUE %}
        //TODO need to malloc a copy and later free
    if (!smedl_assign_opaque(&new_params[{{loop.index0}}].v.o, {{expression(a.params[loop.index0])}})) {
        /* TODO What to do if malloc fails? */
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
if (mon->ef.{{scenario.name}}_flag) {
    switch (mon->{{scenario.name}}_state) {
        {% for state in scenario.all_states if (state, event) in scenario.steps %}
        case STATE_{{spec.name}}_{{scenario.name}}_{{state}}:
            {# Note: We don't try to do anything special if the condition is 1
                (like disable the "else" and further "else if"s) because it
                would complicate the template and the compiler will optimize
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
    mon->ef.{{scenario.name}}_flag = 1;
}
{%- if not loop.last %}


{% endif %}
{% endfor %}
{%- endmacro %}
{# End of event handler macros ********************************************** #}
{% if spec.imported_events is nonempty %}

/* Imported events */
{% for event in spec.imported_events.keys() %}

void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}

    {% endif %}
    /* Finish the macro-step */
    handle_{{spec.name}}_queue(mon);
}
{% endfor %}
{% endif %}
{% if spec.internal_events is nonempty %}

/* Internal events */
{% for event in spec.internal_events.keys() %}

void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}
    {% endif %}
}

void queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    if (!push_event(&mon->event_queue, EVENT_{{spec.name}}_{{event}}, params, aux)) {
        //TODO Out of memory. What now?
    }
}
{% endfor %}
{% endif %}
{% if spec.exported_events is nonempty %}

/* Exported events */
{% for event in spec.exported_events.keys() %}

void execute_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    {% if spec.needs_handler(event) %}
    {{event_handler(event)|indent}}

    {% endif %}
    /* Export the event */
    export_{{spec.name}}_{{event}}(mon, params, aux);
}

void queue_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    if (!push_event(&mon->event_queue, EVENT_{{spec.name}}_{{event}}, params, aux)) {
        //TODO Out of memory. What now?
    }
}

void export_{{spec.name}}_{{event}}({{spec.name}}Monitor *mon, SMEDLValue *params, void *aux) {
    if (mon->callback_{{event}} != NULL) {
        (mon->callback_{{event}})(mon->identities, params, aux);
    }
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
    default_{{spec.name}}_state(&init_state);
    return init_{{spec.name}}_with_state(identities, &init_state);
}

/* Fill the provided {{spec.name}}State
 * with the default initial values for the monitor. Note that strings and
 * opaque data must be free()'d if they are reassigned! The following two
 * functions from smedl_types.h make that simple:
 * - smedl_replace_string()
 * - smedl_replace_opaque() */
void default_{{spec.name}}_state({{spec.name}}State *state) {
    {% for var in spec.state_vars.values() %}
    {% if var.initial_value is not none %}
    {# Strings and opaques must be malloc'd because when they are reassigned,
        the old value is free'd and the new value malloc'd again. See issue
        #48 #}
    {% if var.type is sameas SmedlType.STRING %}
    if (!smedl_assign_string(&state->{{var.name}}, {{var.initial_value}})) {
        /* TODO Out of memory. What now? */
    }
    {% elif var.type is sameas SmedlType.OPAQUE %}
    if (!smedl_assign_opaque(&state->{{var.name}}, {{var.initial_value}})) {
        /* TODO Out of memory. What now? */
    }
    {% else %}
    state->{{var.name}} = {{var.initial_value}};
    {% endif %}
    {% endif %}
    {% endfor %}
}

/* Initialize a {{spec.name}} monitor with the provided state.
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
