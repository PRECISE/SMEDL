//Compile: gcc -o evtatt_mon -std=c99 actions.c monitor_map.c evtatt_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "evtatt_mon.h"

typedef enum { EVTATT_ID } evtatt_identity;
const identity_type evtatt_identity_types[EVTATT_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { EVTATT_SC1_SCENARIO } evtatt_scenario;
typedef enum { EVTATT_SC1_MIN1 } evtatt_sc1_state;
typedef enum { EVTATT_FOO_EVENT } evtatt_event;
typedef enum { EVTATT_DEFAULT } evtatt_error;
const char *evtatt_sc1_states[1] = { "Min1" };
const char **evtatt_states_names[1] = { evtatt_sc1_states };

EvtattMonitor* init_evtatt_monitor( EvtattData *d ) {
    EvtattMonitor* monitor = (EvtattMonitor*)malloc(sizeof(EvtattMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EVTATT_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->state[EVTATT_SC1_SCENARIO] = EVTATT_SC1_MIN1;
    put_evtatt_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void evtatt_foo(EvtattMonitor* monitor, int x) {
  switch (monitor->state[EVTATT_SC1_SCENARIO]) {
    case EVTATT_SC1_MIN1:
      monitor->state[EVTATT_SC1_SCENARIO] = EVTATT_SC1_MIN1;
      break;

    default:
      raise_error("evtatt_sc1", evtatt_states_names[EVTATT_SC1_SCENARIO][monitor->state[EVTATT_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_evtatt_foo(EvtattMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EVTATT_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_evtatt_monitor_maps() {
    if (pthread_mutex_init(&evtatt_monitor_maps_lock, NULL) != 0) {
        printf("\nEvtatt Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < EVTATT_MONITOR_IDENTITIES; i++) {
        evtatt_monitor_maps[i] = (EvtattMonitorMap*)malloc(sizeof(EvtattMonitorMap));
    }
    return 1;
}

int add_evtatt_monitor_to_map(EvtattMonitor *monitor, int identity) {
    EvtattMonitorMap* map = evtatt_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, EVTATT_MONITOR_MAP_SIZE);
    EvtattMonitorRecord* record = (EvtattMonitorRecord*)malloc(sizeof(EvtattMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&evtatt_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&evtatt_monitor_maps_lock);
    return 1;
}

int put_evtatt_monitor(EvtattMonitor *monitor) {
    return add_evtatt_monitor_to_map(monitor, EVTATT_ID);
}

EvtattMonitorRecord* get_evtatt_monitors() {
    EvtattMonitorRecord* results = NULL;
    EvtattMonitorMap* map = evtatt_monitor_maps[0];
    for(int i = 0; i < EVTATT_MONITOR_MAP_SIZE; i++) {
        EvtattMonitorRecord* current = map->list[i];
        while(current != NULL) {
            EvtattMonitorRecord* record = (EvtattMonitorRecord*)malloc(sizeof(EvtattMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

EvtattMonitorRecord* get_evtatt_monitors_by_identity(int identity, int type, void *value) {
    EvtattMonitorRecord* results = NULL;
    EvtattMonitorMap* map = evtatt_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, EVTATT_MONITOR_MAP_SIZE);
    EvtattMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            EvtattMonitorRecord* record = (EvtattMonitorRecord*)malloc(sizeof(EvtattMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

EvtattMonitorRecord* filter_evtatt_monitors_by_identity(EvtattMonitorRecord* before, int identity, void  *value) {
    EvtattMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            EvtattMonitorRecord* record = (EvtattMonitorRecord*)malloc(sizeof(EvtattMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}