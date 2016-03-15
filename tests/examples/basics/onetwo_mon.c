//Compile: gcc -o onetwo_mon -std=c99 actions.c monitor_map.c onetwo_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "onetwo_mon.h"

typedef enum { ONETWOMON_ID } onetwomon_identity;
const identity_type onetwomon_identity_types[ONETWOMON_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { ONETWOMON_SC1_SCENARIO } onetwomon_scenario;
typedef enum { ONETWOMON_SC1_ONETWO, ONETWOMON_SC1_GEN0, ONETWOMON_SC1_TWOONE } onetwomon_sc1_state;
typedef enum { ONETWOMON_FOO_EVENT } onetwomon_event;
typedef enum { ONETWOMON_DEFAULT } onetwomon_error;
const char *onetwomon_sc1_states[3] = { "OneTwo", "Gen0", "TwoOne" };
const char **onetwomon_states_names[1] = { onetwomon_sc1_states };

OnetwomonMonitor* init_onetwomon_monitor( OnetwomonData *d ) {
    OnetwomonMonitor* monitor = (OnetwomonMonitor*)malloc(sizeof(OnetwomonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[ONETWOMON_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->state[ONETWOMON_SC1_SCENARIO] = ONETWOMON_SC1_ONETWO;
    put_onetwomon_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void onetwomon_foo(OnetwomonMonitor* monitor) {
  switch (monitor->state[ONETWOMON_SC1_SCENARIO]) {
    case ONETWOMON_SC1_GEN0:
      monitor->state[ONETWOMON_SC1_SCENARIO] = ONETWOMON_SC1_TWOONE;
      break;

    case ONETWOMON_SC1_ONETWO:
      monitor->state[ONETWOMON_SC1_SCENARIO] = ONETWOMON_SC1_GEN0;
      break;

    default:
      raise_error("onetwomon_sc1", onetwomon_states_names[ONETWOMON_SC1_SCENARIO][monitor->state[ONETWOMON_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_onetwomon_foo(OnetwomonMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, ONETWOMON_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_onetwomon_monitor_maps() {
    if (pthread_mutex_init(&onetwomon_monitor_maps_lock, NULL) != 0) {
        printf("\nOnetwomon Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < ONETWOMON_MONITOR_IDENTITIES; i++) {
        onetwomon_monitor_maps[i] = (OnetwomonMonitorMap*)malloc(sizeof(OnetwomonMonitorMap));
    }
    return 1;
}

int add_onetwomon_monitor_to_map(OnetwomonMonitor *monitor, int identity) {
    OnetwomonMonitorMap* map = onetwomon_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, ONETWOMON_MONITOR_MAP_SIZE);
    OnetwomonMonitorRecord* record = (OnetwomonMonitorRecord*)malloc(sizeof(OnetwomonMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&onetwomon_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&onetwomon_monitor_maps_lock);
    return 1;
}

int put_onetwomon_monitor(OnetwomonMonitor *monitor) {
    return add_onetwomon_monitor_to_map(monitor, ONETWOMON_ID);
}

OnetwomonMonitorRecord* get_onetwomon_monitors() {
    OnetwomonMonitorRecord* results = NULL;
    OnetwomonMonitorMap* map = onetwomon_monitor_maps[0];
    for(int i = 0; i < ONETWOMON_MONITOR_MAP_SIZE; i++) {
        OnetwomonMonitorRecord* current = map->list[i];
        while(current != NULL) {
            OnetwomonMonitorRecord* record = (OnetwomonMonitorRecord*)malloc(sizeof(OnetwomonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

OnetwomonMonitorRecord* get_onetwomon_monitors_by_identity(int identity, int type, void *value) {
    OnetwomonMonitorRecord* results = NULL;
    OnetwomonMonitorMap* map = onetwomon_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, ONETWOMON_MONITOR_MAP_SIZE);
    OnetwomonMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            OnetwomonMonitorRecord* record = (OnetwomonMonitorRecord*)malloc(sizeof(OnetwomonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

OnetwomonMonitorRecord* filter_onetwomon_monitors_by_identity(OnetwomonMonitorRecord* before, int identity, void  *value) {
    OnetwomonMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            OnetwomonMonitorRecord* record = (OnetwomonMonitorRecord*)malloc(sizeof(OnetwomonMonitorRecord));
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