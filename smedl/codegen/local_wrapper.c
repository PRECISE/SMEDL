#if DEBUG > 0
#include <stdio.h>
#endif
#include <stdlib.h>
#include "smedl_types.h"
#include "monitor_map.h"
#include "{{mon.syncset.name}}_global_wrapper.h"
#include "{{mon.name}}_local_wrapper.h"
#include "{{spec.name}}_mon.h"

{% if mon.params is nonempty %}
static {{mon.name}}Record dummy_rec;
/* Used as error response for get_{{mon.name}}_record() since it can
 * legitimately return NULL */
static {{mon.name}}Record *INVALID_RECORD = &dummy_rec;

/* {{mon.name}} Monitor Maps - One AVL tree for each identity */
{% for i in range(mon.params|length) %}
static {{mon.name}}Record *monitor_map_{{i}} = NULL;
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
    /* Reserved for future use, but no need to actually do anything at this
     * time. Monitor maps are already initialized to NULL by being of static
     * storage duration. */
    return 1;
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
    {{mon.name}}Record *records, *next;
    {% for i in range(mon.params|length) %}

    {% if loop.last %}
    /* Free records, monitors, identities, and map for monitor_map_{{i}} */
    {% else %}
    /* Free records and map for monitor_map_{{i}} */
    {% endif %}
    records = ({{mon.name}}Record *) monitor_map_all((SMEDLRecordBase *) monitor_map_{{i}});
    while (records != NULL) {
        {% if loop.last %}
        free(records->mon->identities);
        free(records->mon);
        {% endif %}
        next = ({{mon.name}}Record *) records->r.next;
        free(records);
        records = next;
    }
    monitor_map_{{i}} = NULL;
    {% endfor %}
    {% else %}
    free_{{spec.name}}_monitor(monitor);
    {% endif %}
}

/* Creation interface - Instantiate a new {{mon.name}} monitor.
 * Return nonzero on success or if monitor already exists, zero on failure.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 *   Must be fully specified; no wildcards.
 * init_state - A pointer to a {{spec.name}}State containing
 *   the initial state variable values for this monitor. A default initial
 *   state can be retrieved with default_{{spec.name}}_state()
 *   and then just the desired variables can be updated. */
int create_{{mon.name}}_monitor(SMEDLValue *identities, {{spec.name}}State *init_state) {
    {% if mon.params is nonempty %}
    /* Check if monitor with identities already exists */
    if (check_{{mon.name}}_monitors(identities)) {
        return 1;
    }

    /* Initialize new monitor with identities and state */
    SMEDLValue *ids_copy = smedl_copy_array(identities, {{mon.params|length}});
    if (ids_copy == NULL) {
        /* malloc fail */
        return 0;
    }
    {{spec.name}}Monitor *mon = init_{{spec.name}}_with_state(ids_copy, init_state);
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

int process_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
#if DEBUG >= 4
    fprintf(stderr, "Local wrapper '{{mon.name}}' processing event '{{event}}'\n");
#endif
    {% if mon.params is nonempty %}
    /* Fetch the monitors to send the event to or do dynamic instantiation if
     * necessary */
    {{mon.name}}Record *records = get_{{mon.name}}_monitors(identities);
    if (records == INVALID_RECORD) {
        /* malloc fail */
        return 0;
    }

    /* Send the event to each monitor */
    int success = 1;
    while (records != NULL) {
        {{spec.name}}Monitor *mon = records->mon;
        records = ({{mon.name}}Record *) records->r.next;
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
    remove_{{mon.name}}_monitor(mon->identities);
    return 1;
}

/* Add the provided monitor to the monitor maps. Return a
 * {{mon.name}}Record, or NULL if unsuccessful. */
{{mon.name}}Record * add_{{mon.name}}_monitor({{spec.name}}Monitor *mon) {
    {% for i in range(mon.params|length) %}
    /* Identity {{i}} */
    {{mon.name}}Record *rec{{i}};
    rec{{i}} = malloc(sizeof({{mon.name}}Record));
    if (rec{{i}} == NULL) {
        /* malloc fail */
        goto add_fail_{{i}};
    }
    rec{{i}}->mon = mon;
    rec{{i}}->r.key = mon->identities[{{i}}];
    monitor_map_insert((SMEDLRecordBase **) &monitor_map_{{i}}, (SMEDLRecordBase *) rec{{i}});

    {% endfor %}
    return rec0;

    {% for i in range(mon.params|length - 1, 0, -1) %}
add_fail_{{i}}:
    monitor_map_remove((SMEDLRecordBase **) &monitor_map_{{i-1}}, (SMEDLRecordBase *) rec{{i-1}});
    free(rec{{i-1}});
    {% endfor %}
add_fail_0:
    return NULL;
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
 * Returns a linked list of {{mon.name}}Record (which may be empty, i.e. NULL).
 * If dynamic instantiation fails, returns INVALID_RECORD. */
{{mon.name}}Record * get_{{mon.name}}_monitors(SMEDLValue *identities) {
    /* Fetch the candidate list using the monitor map for the first
     * non-wildcard */
    SMEDLRecordBase *candidates = NULL;
    int all_wildcards = 0;
    {% for i in range(mon.params|length) %}
    {%+ if not loop.first %}} else {%+ endif %}if (identities[{{i}}].t != SMEDL_NULL) {
        candidates = monitor_map_lookup((SMEDLRecordBase *) monitor_map_{{i}}, identities[{{i}}]);
    {% if loop.last %}
    } else {
    {% endif %}
    {% endfor %}
        /* All identities were wildcards. */
        all_wildcards = 1;
    }

    {{mon.name}}Record *result;
    if (all_wildcards) {
        /* Fetch *all* records */
        result = ({{mon.name}}Record *) monitor_map_all((SMEDLRecordBase *) monitor_map_0);
    } else {
        /* Filter down to candidates that match the full identity list */
        result = NULL;
        for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
            if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities, {{mon.params|length}})) {
                rec->next = (SMEDLRecordBase *) result;
                result = ({{mon.name}}Record *) rec;
            }
        }
    }

    /* If there are no matches and identity list is fully specified (no
     * wildcards), do dynamic instantiation. */
    if (result == NULL) {
        int dynamic_instantiation = 1;
        for (size_t i = 0; i < {{mon.params|length}}; i++) {
            if (identities[i].t == SMEDL_NULL) {
                dynamic_instantiation = 0;
            }
        }

        if (dynamic_instantiation) {
#if DEBUG >= 4
            fprintf(stderr, "Dynamic instantiation for '{{mon.name}}'\n");
#endif
            SMEDLValue *ids_copy = smedl_copy_array(identities, {{mon.params|length}});
            if (ids_copy == NULL) {
                /* malloc fail */
                return INVALID_RECORD;
            }
            {{spec.name}}Monitor *mon = init_{{spec.name}}_monitor(ids_copy);
            if (mon == NULL) {
                /* malloc fail */
                smedl_free_array(ids_copy, {{mon.params|length}});
                return INVALID_RECORD;
            }
            setup_{{mon.name}}_callbacks(mon);
            result = add_{{mon.name}}_monitor(mon);
            if (result == NULL) {
                /* malloc fail */
                free_{{spec.name}}_monitor(mon);
                smedl_free_array(ids_copy, {{mon.params|length}});
                return INVALID_RECORD;
            }
            result->r.next = NULL;
        }
    }

    return result;
}

/* Check if a monitor with the given identities is present. Return nonzero if
 * so, zero if not. The identities must be fully specified (no wildcards). */
int check_{{mon.name}}_monitors(SMEDLValue *identities) {
    /* Fetch monitors with matching first identity */
    SMEDLRecordBase *candidates = monitor_map_lookup((SMEDLRecordBase *) monitor_map_0, identities[0]);

    /* Check if any of the candidates match the full identity list */
    for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
        if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities, {{mon.params|length}})) {
            return 1;
        }
    }

    return 0;
}

/* Remove a monitor with the given identities from the monitor maps. The
 * identities must be fully specified (no wildcards). */
void remove_{{mon.name}}_monitor(SMEDLValue *identities) {
    SMEDLRecordBase *candidates;
    {% for i in range(mon.params|length) %}

    /* Fetch matching monitors from monitor map {{i}}, then iterate through to
     * find and remove the full match */
    candidates = monitor_map_lookup((SMEDLRecordBase *) monitor_map_{{i}}, identities[{{i}}]);
    for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
        if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities, {{mon.params|length}})) {
            monitor_map_remove((SMEDLRecordBase **) &monitor_map_{{i}}, rec);
            {% if loop.last %}
            /* Free the monitor itself before freeing the last record */
            {{spec.name}}Monitor *mon = (({{mon.name}}Record *) rec)->mon;
            smedl_free_array(mon->identities, {{mon.params|length}});
            free_{{spec.name}}_monitor(mon);
            {% endif %}
            free(rec);
            break;
        }
    }
    {% endfor %}
}
{% endif %}
