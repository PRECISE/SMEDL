#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include "smedl_types.h"
#include "monitor_map.h"
#include "{{mon.syncset.name}}_global_wrapper.h"
#include "{{mon.name}}_local_wrapper.h"
#include "{{spec.name}}_mon.h"

{% macro mon_map_name(param_set) -%}
{%- if param_set == mon.full_param_subset -%}
monitor_map_all
{%- elif param_set == () -%}
monitor_map_none
{%- else -%}
monitor_map_{% for i in param_set %}{% if not loop.first %}_{% endif %}{{i}}{% endfor %}
{%- endif -%}
{%- endmacro %}
{% macro mon_hash_name(param_set) -%}
{%- if param_set == mon.full_param_subset -%}
hash_all
{%- elif param_set == () -%}
hash_none
{%- else -%}
hash_{% for i in param_set %}{% if not loop.first %}_{% endif %}{{i}}{% endfor %}
{%- endif -%}
{%- endmacro %}
{% macro mon_equals_name(param_set) -%}
{%- if param_set == mon.full_param_subset -%}
equals_all
{%- elif param_set == () -%}
equals_none
{%- else -%}
equals_{% for i in param_set %}{% if not loop.first %}_{% endif %}{{i}}{% endfor %}
{%- endif -%}
{%- endmacro %}
{# /************************************************************************/ #}
{% if mon.params is nonempty %}
/* {{mon.name}} Monitor Maps - One for each subset of non-wildcard identities
 * used for lookups.
 *
 * For fast lookups, SMEDL keeps a monitor map for each subset of non-wildcard
 * identities used. For example, with the following connections:
 *
 *     ev1 => Mon1[$0, $1, $2].ev1();
 *     ev2 => Mon1[$0, *, $1].ev2();
 *
 * There would be two monitor maps: one that hashes all three identities, and
 * one that hashes the first and third. For the latter, any monitors with
 * identical first and third identities would be grouped together in the hash
 * table (as a linked list).
 *
 * The monitor map that hashes all identities (i.e. no wildcards) is always
 * called "monitor_map_all". The monitor map that stores all monitors in the
 * same bucket (i.e. all identities are wildcard), if present, is called
 * "monitor_map_none".
 */
{% for param_set in mon.param_subsets %}
static MonitorMap {{mon_map_name(param_set)}};
{% endfor %}

/* Monitor map hash functions - One for each monitor map */
{% for param_set in mon.param_subsets %}

static uint64_t {{mon_hash_name(param_set)}}(SMEDLValue *ids) {
    murmur_state s = MURMUR_INIT(0);
    {% for param in param_set %}
    {% if mon.params[param] is sameas SmedlType.INT %}
    murmur(&ids[{{param}}].v.i, sizeof(ids[{{param}}].v.i), &s);
    {% elif mon.params[param] is sameas SmedlType.FLOAT %}
    murmur(&ids[{{param}}].v.d, sizeof(ids[{{param}}].v.d), &s);
    {% elif mon.params[param] is sameas SmedlType.CHAR %}
    murmur(&ids[{{param}}].v.c, sizeof(ids[{{param}}].v.c), &s);
    {% elif mon.params[param] is sameas SmedlType.STRING %}
    murmur(ids[{{param}}].v.s, strlen(ids[{{param}}].v.s), &s);
    {% elif mon.params[param] is sameas SmedlType.POINTER %}
    murmur(&ids[{{param}}].v.p, sizeof(ids[{{param}}].v.p), &s);
    {% elif mon.params[param] is sameas SmedlType.OPAQUE %}
    murmur(ids[{{param}}].v.o.data, ids[{{param}}].v.o.size, &s);
    {% endif %}
    {% endfor %}
    return murmur_f(&s);
}
{% endfor %}

/* Monitor map equals functions - One for each monitor map */
{% for param_set in mon.param_subsets %}

static int {{mon_equals_name(param_set)}}(SMEDLValue *ids1, SMEDLValue *ids2) {
    {% for param in param_set %}
    {% if mon.params[param] is sameas SmedlType.INT %}
    if (ids1[{{param}}].v.i != ids2[{{param}}].v.i) {
        return 0;
    }
    {% elif mon.params[param] is sameas SmedlType.FLOAT %}
    if (ids1[{{param}}].v.d != ids2[{{param}}].v.d) {
        return 0;
    }
    {% elif mon.params[param] is sameas SmedlType.CHAR %}
    if (ids1[{{param}}].v.c != ids2[{{param}}].v.c) {
        return 0;
    }
    {% elif mon.params[param] is sameas SmedlType.STRING %}
    if (strcmp(ids1[{{param}}].v.s, ids2[{{param}}].v.s)) {
        return 0;
    }
    {% elif mon.params[param] is sameas SmedlType.POINTER %}
    if (ids1[{{param}}].v.p != ids2[{{param}}].v.p) {
        return 0;
    }
    {% elif mon.params[param] is sameas SmedlType.OPAQUE %}
    if (!smedl_opaque_equals(ids1[{{param}}].v.o, ids2[{{param}}].v.o)) {
        return 0;
    }
    {% endif %}
    {% endfor %}
    return 1;
}
{% endfor %}
{% else %}
/* Singleton monitor */
static {{spec.name}}Monitor *monitor;
{% endif %}

/* Register the global wrapper's export callbacks with the monitor */
static void setup_{{mon.name}}_callbacks({{spec.name}}Monitor *mon) {
    {% for event in spec.exported_events.keys() %}
    register_{{spec.name}}_{{event}}(mon, raise_{{mon.name}}_{{event}});
    {% endfor %}
    {% if mon.params is nonempty %}
    registercleanup_{{spec.name}}(mon, recycle_{{mon.name}}_monitor);
    {% endif %}
}

/* Initialization interface - Initialize the local wrapper. Must be called once
 * before creating any monitors or importing any events.
 * Return nonzero on success, zero on failure. */
int init_{{mon.name}}_local_wrapper() {
    {% if mon.params is nonempty %}
    {% for param_set in mon.param_subsets %}
    if (!monitormap_init(&{{mon_map_name(param_set)}}, offsetof({{spec.name}}Monitor, identities), {{mon_hash_name(param_set)}}, {{mon_equals_name(param_set)}})) {
        goto fail_init_{{mon_map_name(param_set)}};
    }
    {% endfor %}

    return 1;

    {% for param_set in mon.param_subsets|reverse %}
    {% if not loop.first %}
    monitormap_free(&{{mon_map_name(param_set)}}, 0);
    {% endif %}
fail_init_{{mon_map_name(param_set)}}:
    {% endfor %}
    return 0;
    {% else %}
    /* Initialize the singleton */
    monitor = init_{{spec.name}}_monitor(NULL);
    if (monitor == NULL) {
        return 0;
    }
    setup_{{mon.name}}_callbacks(monitor);
    return 1;
    {% endif %}
}

/* Cleanup interface - Tear down and free the resources used by this local
 * wrapper and all the monitors it manages */
void free_{{mon.name}}_local_wrapper() {
    {% if mon.params is nonempty %}
    MonitorInstance *instances = monitormap_free(&monitor_map_all, 1);
    {% for param_set in mon.param_subsets
        if param_set != mon.full_param_subset %}
    monitormap_free(&{{mon_map_name(param_set)}}, 0);
    {% endfor %}

    while (instances != NULL) {
        MonitorInstance *tmp = instances->next;
        smedl_free_array((({{spec.name}}Monitor *) instances->mon)->identities, {{mon.params|length}});
        free_{{spec.name}}_monitor(instances->mon);
        free(instances);
        instances = tmp;
    }
    {% else %}
    free_{{spec.name}}_monitor(monitor);
    {% endif %}
}

/* Creation interface - Instantiate a new {{mon.name}} monitor.
 * Return nonzero on success or if monitor already exists, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 *   Must be fully specified; no wildcards. */
int create_{{mon.name}}(SMEDLValue *identities) {
    {% if mon.params is nonempty %}
    /* Check if monitor with identities already exists */
    if (monitormap_lookup(&monitor_map_all, identities) != NULL) {
#if DEBUG >= 4
        fprintf(stderr, "Local wrapper '{{mon.name}}' skipping explicit creation for existing monitor\n");
#endif
        return 1;
    }
#if DEBUG >= 4
    fprintf(stderr, "Local wrapper '{{mon.name}}' doing explicit creation\n");
#endif

    /* Initialize new monitor with identities and state */
    SMEDLValue *ids_copy = smedl_copy_array(identities, {{mon.params|length}});
    if (ids_copy == NULL) {
        /* malloc fail */
        return 0;
    }
    {{spec.name}}Monitor *mon = init_{{spec.name}}_monitor(ids_copy);
    if (mon == NULL) {
        /* malloc fail */
        smedl_free_array(ids_copy, {{mon.params|length}});
        return 0;
    }
    setup_{{mon.name}}_callbacks(mon);

    /* Store monitor in maps */
    if (add_{{mon.name}}_monitor(mon) == NULL) {
        /* malloc fail */
        free_{{spec.name}}_monitor(mon);
        smedl_free_array(ids_copy, {{mon.params|length}});
        return 0;
    }
    {% else %}
    /* Singleton monitor - This is a no-op */
    {% endif %}
    return 1;
}

/* State variable interface - Set the value of the respective state variable.
 * Intended to be used right after monitor creation.
 * Return nonzero on success, zero if the monitor does not exist or malloc
 * failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 * value - The value to assign to the state variable. */
{% for var in spec.state_vars.values() %}

int set_{{mon.name}}_{{var.name}}(SMEDLValue *identities, SMEDLValue value) {
    {% if mon.params is nonempty %}
    MonitorInstance *mon_inst = monitormap_lookup(&monitor_map_all, identities);
    if (mon_inst == NULL) {
        return 0;
    }
    {{spec.name}}Monitor *mon = mon_inst->mon;
    return setvar_{{spec.name}}_{{var.name}}(mon, value);
    {% else %}
    /* Singleton monitor - This is a no-op */
    {% endif %}
    return 1;
}
{% endfor %}

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 * Return nonzero on success, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 *   Wildcards can be represented with a SMEDLValue of type SMEDL_NULL.
 * params - An array of SMEDLValue, one for each parameter of the event.
 * aux - Extra data that is passed through to exported events unchanged. */
{% for event in spec.imported_events.keys() %}

int perform_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Local wrapper '{{mon.name}}' processing event '{{event}}'\n");
#endif
    {% if mon.params is nonempty %}
    /* Fetch the monitors to send the event to or do dynamic instantiation if
     * necessary */
    MonitorInstance *instances = get_{{mon.name}}_monitors(identities);
    if (instances == INVALID_INSTANCE) {
        /* malloc fail */
        return 0;
    }

    /* Send the event to each monitor */
    int success = 1;
    while (instances != NULL) {
        {{spec.name}}Monitor *mon = instances->mon;
        instances = instances->next;
        if (!execute_{{spec.name}}_{{event}}(mon, params, aux)) {
            success = 0;
        }
    }
    return success;
    {% else %}
    /* Send event to the singleton monitor */
    return execute_{{spec.name}}_{{event}}(monitor, params, aux);
    {% endif %}
}
{% endfor %}
{% if mon.params is nonempty %}

/* Recycle a monitor instance - Used as the callback for when final states are
 * reached in the monitor. Return nonzero if successful, zero on failure. */
int recycle_{{mon.name}}_monitor({{spec.name}}Monitor *mon) {
#if DEBUG >= 4
        fprintf(stderr, "Recycling an instance of '{{mon.name}}'\n");
#endif
    monitormap_remove(&monitor_map_all, mon);
    smedl_free_array(mon->identities, {{mon.params|length}});
    free_{{spec.name}}_monitor(mon);
    return 1;
}

/* Add the provided monitor to the monitor maps. Return a
 * MonitorInstance, or NULL if unsuccessful. */
MonitorInstance * add_{{mon.name}}_monitor({{spec.name}}Monitor *mon) {
    MonitorInstance *prev_inst = NULL;
    MonitorMap *prev_map = NULL;
    MonitorInstance *inst;
    {% for param_set in mon.param_subsets
        if param_set != mon.full_param_subset %}

    inst = monitormap_insert(&{{mon_map_name(param_set)}}, mon, prev_inst, prev_map);
    if (inst == NULL) {
        {% if not loop.first %}
        monitormap_removeinst(prev_map, prev_inst);
        {% endif %}
        return NULL;
    }
    prev_inst = inst;
    prev_map = &{{mon_map_name(param_set)}};
    {% endfor %}

    inst = monitormap_insert(&monitor_map_all, mon, prev_inst, prev_map);
    if (inst == NULL) {
        {% if mon.param_subsets|length > 1 %}
        monitormap_removeinst(prev_map, prev_inst);
        {% endif %}
        return NULL;
    }

    return inst;
}

/* Fetch a list of monitor instances matching the given identities.
 *
 * Identities are given as an array of SMEDLValue. Wildcards for multicast
 * are indicated with SMEDLValues with type SMEDL_NULL.
 *
 * If there are no matching monitor instances but the identity list is fully
 * specified (i.e. there are no wildcards), create an instance with those
 * identities and return it.
 *
 * Returns a linked list of MonitorInstance (which may be empty, i.e. NULL).
 * If dynamic instantiation fails, returns INVALID_INSTANCE. */
{% macro pick_mon_map(tree) %}
{% if tree is mapping %}
if (identities[{{tree.idx}}].t == SMEDL_NULL) {
    {{pick_mon_map(tree.wild)|indent}}
} else {
    {{pick_mon_map(tree.bound)|indent}}
}
{%- else %}
instances = monitormap_lookup(&{{mon_map_name(tree)}}, identities);
{%- if tree == mon.full_param_subset %}

dynamic_instantiation = 1;
{%- endif %}
{% endif %}
{% endmacro %}
MonitorInstance * get_{{mon.name}}_monitors(SMEDLValue *identities) {
    /* Look up from the proper monitor map */
    MonitorInstance *instances;
    int dynamic_instantiation = 0;
    {{pick_mon_map(mon.param_subsets_tree)|indent}}

    /* Do dynamic instantiation if wildcards were fully specified and there
     * are no matching monitors */
    if (instances == NULL && dynamic_instantiation) {
#if DEBUG >= 4
        fprintf(stderr, "Dynamic instantiation for '{{mon.name}}'\n");
#endif
        SMEDLValue *ids_copy = smedl_copy_array(identities, {{mon.params|length}});
        if (ids_copy == NULL) {
            /* malloc fail */
            return INVALID_INSTANCE;
        }
        {{spec.name}}Monitor *mon = init_{{spec.name}}_monitor(ids_copy);
        if (mon == NULL) {
            /* malloc fail */
            smedl_free_array(ids_copy, {{mon.params|length}});
            return INVALID_INSTANCE;
        }
        setup_{{mon.name}}_callbacks(mon);
        instances = add_{{mon.name}}_monitor(mon);
        if (instances == NULL) {
            /* malloc fail */
            free_{{spec.name}}_monitor(mon);
            smedl_free_array(ids_copy, {{mon.params|length}});
            return INVALID_INSTANCE;
        }
    }

    return instances;
}
{% endif %}
