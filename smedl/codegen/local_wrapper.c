#include "smedl_types.h"
#include "{{spec.name}}_mon.h"

//TODO How does this work if the monitor has no identities?

/* {{mon.name}} Monitor Maps - One AVL tree for each identity */
{% for i in range(len(mon.params)) %}
static {{mon.name}}Record *monitor_map_{{i}} = NULL;
{% endfor %}

/* Initialization interface - Initialize the local wrapper. Must be called once
 * before creating any monitors or importing any events. */
void init_{{mon.name}}_local_wrapper() {
    /* Reserved for future use, but no need to actually do anything at this
     * time. Monitor maps are already initialized to NULL by being of static
     * storage duration (because they are global, not because they are declared
     * static). */
}

/* Cleanup interface - Tear down and free the resources used by this local
 * wrapper and all the monitors it manages */
void free_{{mon.name}}_local_wrapper() {
    //TODO
}

/* Creation interface - Instantiate a new {{mon.name}} monitor.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 *   Must be fully specified; no wildcards.
 * init_state - A pointer to a {{spec.name}}State containing
 *   the initial state variable values for this monitor. A default initial
 *   state can be retrieved with default_{{spec.name}}_state()
 *   and then just the desired variables can be updated. */
void create_{{mon.name}}_monitor(SMEDLValue *identities, {{spec.name}}State *init_state) {
    /* Check if monitor with identities already exists */
    if (check_{{mon.name}}_monitors(identities)) {
        return;
    }

    /* Initialize new monitor with identities and state */
    //TODO Identities must be freed when monitor is freed
    SMEDLValue *ids_copy = smedl_copy_array(identities, {{len(mon.params)}});
    if (ids_copy == NULL) {
        //TODO Malloc failed. What do we do here?
    }
    {{spec.name}}Monitor *mon = init_{{spec.name}}_with_state(ids_copy, init_state);

    /* Store monitor in maps */
    add_{{mon.name}}_monitor(mon);
}

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
 *   Wildcards can be represented with a SMEDLValue of type SMEDL_NULL.
 * params - An array of SMEDLValue, one for each parameter of the event.
 * aux - Extra data that is passed through to exported events unchanged. */
{% for event in spec.imported_events.keys() %}

void process_{{mon.name}}_{{event}}(SMEDLValue *identities, SMEDLValue *params, SMEDLAux aux) {
    /* Fetch the monitors to send the event to or do dynamic instantiation if
     * necessary */
    {{mon.name}}Record records = get_{{mon.name}}_monitors(identities);

    /* Send the event to each monitor */
    while (records != NULL) {
        {{spec.name}}Monitor *mon = records->mon;
        execute_{{spec.name}}_{{event}}(mon, params, aux);
        records = records->next;
    }
}
{% endfor %}

/* Add the provided monitor to the monitor maps */
void add_{{mon.name}}_monitor({{spec.name}}Monitor *mon) {
    {{mon.name}}Record *rec;

    {% for i in range(len(mon.params)) %}
    /* Identity {{i}} */
    rec = malloc(sizeof({{mon.name}}Record));
    if (rec == NULL) {
        //TODO malloc fail, what do we do?
    }
    rec->mon = mon;
    rec->r.key = mon->identities[{{i}}];
    monitor_map_insert(&monitor_map_{{i}}, rec);
    {% if not loop.last %}

    {% endif %}
    {% endfor %}
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
 * Returns a linked list of {{mon.name}}Record. */
{{mon.name}}Record * get_{{mon.name}}_monitors(SMEDLValue *identities) {
    /* Fetch the candidate list using the monitor map for the first
     * non-wildcard */
    SMEDLRecordBase *candidates = NULL;
    int all_wildcards = 0;
    {% for i in range(len(mon.params)) %}
    {%+ if not loop.last +%}} else {%+ endif +%}if (identities[i].t != SMEDL_NULL) {
        candidates = monitor_map_lookup(monitor_map_{{i}}, identities[{{i}}]);
    {% if loop.last %}
    } else {
    {% endif %}
    {% endfor %}
        /* All identities were wildcards. */
        all_wildcards = 1;
    }

    if (all_wildcards) {
        /* Fetch *all* records */
        candidates = monitor_map_all(monitor_map_0);
    } else {
        /* Filter down to candidates that match the full identity list */
        {{mon.name}}Record *result = NULL;
        for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
            if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities)) {
                rec->next = (SMEDLRecordBase *) result;
                result = ({{mon.name}}Record *) rec;
            }
        }
    }

    /* If there are no matches and identity list is fully specified (no
     * wildcards), do dynamic instantiation. */
    if (result == NULL) {
        int dynamic_instantiation = 1;
        for (size_t i = 0; i < {{len(mon.params)}}; i++) {
            if (identities[i].t == SMEDL_NULL) {
                dynamic_instantiation = 0;
            }
        }

        if (dynamic_instantiation) {
            SMEDLValue *ids_copy = smedl_copy_array(identities, {{len(mon.params)}});
            if (ids_copy == NULL) {
                //TODO Malloc failed. What do we do here?
            }
            {{spec.name}}Monitor *mon = init_{{spec.name}}_monitor(ids_copy);
            add_{{mon.name}}_monitor(mon);
        }
    }
    
    return result;
}

/* Check if a monitor with the given identities is present. Return nonzero if
 * so, zero if not. The identities must be fully specified (no wildcards). */
int check_{{mon.name}}_monitors(SMEDLValue *identities) {
    /* Fetch monitors with matching first identity */
    SMEDLRecordBase *candidates = monitor_map_lookup(monitor_map_0, identities[0]);

    /* Check if any of the candidates match the full identity list */
    for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
        if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities)) {
            return 1;
        }
    }

    return 0;
}

/* Remove a monitor with the given identities from the monitor maps. The
 * identities must be fully specified (no wildcards). */
void remove_{{mon.name}}_monitor(SMEDLValue *identities) {
    SMEDLRecordBase *candidates;
    {% for i in range(len(mon.params)) %}

    /* Fetch matching monitors from monitor map {{i}}, then iterate through to
     * find and remove the full match */
    candidates = monitor_map_lookup(monitor_map_{{i}}, identities[{{i}}]);
    for (SMEDLRecordBase *rec = candidates; rec != NULL; rec = rec->equal) {
        if (smedl_equal_array(identities, (({{mon.name}}Record *) rec)->mon->identities)) {
            monitor_map_remove(rec);
            {% if loop.last %}
            /* Free the monitor itself before freeing the last record */
            {{spec.name}}Monitor *mon = (({{mon.name}}Record *) rec)->mon;
            free(mon->identities);
            free(mon);
            {% endif %}
            free(rec);
        }
    }
    {% endfor %}
}
