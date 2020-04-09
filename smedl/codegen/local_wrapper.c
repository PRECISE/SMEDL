#include "smedl_types.h"
#include "{{spec.name}}_mon.h"

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
    {{spec.name}}Monitor *mon = init_{{spec.name}}_with_state(identities, init_state);

    /* Store monitor in maps */
    add_{{mon.name}}_monitor(mon);
}

/* Event import interfaces - Send the respective event to the monitor(s) and
 * potentially perform dynamic instantiation.
 *
 * Parameters:
 * identites - An array of SMEDLValue of the proper length for this monitor.
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
    //TODO
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
    //TODO
}

/* Check if a monitor with the given identities is present. Return nonzero if
 * so, zero if not. */
int check_{{mon.name}}_monitors(SMEDLValue *identities) {
    //TODO
}

/* Remove a monitor with the given identities from the monitor maps */
void remove_{{mon.name}}_monitor(SMEDLValue *identities) {
    //TODO
}
