//Compile: gcc -o minimal_mon -std=c99 actions.c monitor_map.c minimal_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "minimal_mon.h"

typedef enum { MINIMAL_ID } minimal_identity;
const identity_type minimal_identity_types[MINIMAL_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { MINIMAL_SC1_SCENARIO } minimal_scenario;
typedef enum { MINIMAL_SC1_MIN } minimal_sc1_state;
typedef enum { MINIMAL_FOO_EVENT } minimal_event;
typedef enum { MINIMAL_DEFAULT } minimal_error;
const char *minimal_sc1_states[1] = { "Min" };
const char **minimal_states_names[1] = { minimal_sc1_states };

MinimalMonitor* init_minimal_monitor( MinimalData *d ) {
    MinimalMonitor* monitor = (MinimalMonitor*)malloc(sizeof(MinimalMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[MINIMAL_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->state[MINIMAL_SC1_SCENARIO] = MINIMAL_SC1_MIN;
    put_minimal_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void minimal_foo(MinimalMonitor* monitor) {
  switch (monitor->state[MINIMAL_SC1_SCENARIO]) {
    case MINIMAL_SC1_MIN:
      monitor->state[MINIMAL_SC1_SCENARIO] = MINIMAL_SC1_MIN;
      break;

    default:
      raise_error("minimal_sc1", minimal_states_names[MINIMAL_SC1_SCENARIO][monitor->state[MINIMAL_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_minimal_foo(MinimalMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, MINIMAL_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_minimal_monitor_maps() {
    if (pthread_mutex_init(&minimal_monitor_maps_lock, NULL) != 0) {
        printf("\nMinimal Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < MINIMAL_MONITOR_IDENTITIES; i++) {
        minimal_monitor_maps[i] = (MinimalMonitorMap*)malloc(sizeof(MinimalMonitorMap));
    }
    return 1;
}

int add_minimal_monitor_to_map(MinimalMonitor *monitor, int identity) {
    MinimalMonitorMap* map = minimal_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, MINIMAL_MONITOR_MAP_SIZE);
    MinimalMonitorRecord* record = (MinimalMonitorRecord*)malloc(sizeof(MinimalMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&minimal_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&minimal_monitor_maps_lock);
    return 1;
}

int put_minimal_monitor(MinimalMonitor *monitor) {
    return add_minimal_monitor_to_map(monitor, MINIMAL_ID);
}

MinimalMonitorRecord* get_minimal_monitors() {
    MinimalMonitorRecord* results = NULL;
    MinimalMonitorMap* map = minimal_monitor_maps[0];
    for(int i = 0; i < MINIMAL_MONITOR_MAP_SIZE; i++) {
        MinimalMonitorRecord* current = map->list[i];
        while(current != NULL) {
            MinimalMonitorRecord* record = (MinimalMonitorRecord*)malloc(sizeof(MinimalMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

MinimalMonitorRecord* get_minimal_monitors_by_identity(int identity, int type, void *value) {
    MinimalMonitorRecord* results = NULL;
    MinimalMonitorMap* map = minimal_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, MINIMAL_MONITOR_MAP_SIZE);
    MinimalMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            MinimalMonitorRecord* record = (MinimalMonitorRecord*)malloc(sizeof(MinimalMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

MinimalMonitorRecord* filter_minimal_monitors_by_identity(MinimalMonitorRecord* before, int identity, void  *value) {
    MinimalMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            MinimalMonitorRecord* record = (MinimalMonitorRecord*)malloc(sizeof(MinimalMonitorRecord));
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