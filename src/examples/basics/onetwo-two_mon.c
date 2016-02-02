//Compile: gcc -o onetwo-two_mon -std=c99 actions.c monitor_map.c onetwo-two_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "onetwo-two_mon.h"

typedef enum { ONETWOTWO_ID } onetwotwo_identity;
const identity_type onetwotwo_identity_types[ONETWOTWO_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { ONETWOTWO_SC1_SCENARIO } onetwotwo_scenario;
typedef enum { ONETWOTWO_SC1_ONETWO, ONETWOTWO_SC1_GEN0 } onetwotwo_sc1_state;
typedef enum { ONETWOTWO_FOO_EVENT, ONETWOTWO_BAR_EVENT } onetwotwo_event;
typedef enum { ONETWOTWO_DEFAULT } onetwotwo_error;
const char *onetwotwo_sc1_states[2] = { "OneTwo", "Gen0" };
const char **onetwotwo_states_names[1] = { onetwotwo_sc1_states };

OnetwotwoMonitor* init_onetwotwo_monitor( OnetwotwoData *d ) {
    OnetwotwoMonitor* monitor = (OnetwotwoMonitor*)malloc(sizeof(OnetwotwoMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[ONETWOTWO_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->state[ONETWOTWO_SC1_SCENARIO] = ONETWOTWO_SC1_ONETWO;
    put_onetwotwo_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void onetwotwo_foo(OnetwotwoMonitor* monitor) {
  switch (monitor->state[ONETWOTWO_SC1_SCENARIO]) {
    case ONETWOTWO_SC1_ONETWO:
      monitor->state[ONETWOTWO_SC1_SCENARIO] = ONETWOTWO_SC1_GEN0;
      break;

    default:
      raise_error("onetwotwo_sc1", onetwotwo_states_names[ONETWOTWO_SC1_SCENARIO][monitor->state[ONETWOTWO_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_onetwotwo_foo(OnetwotwoMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, ONETWOTWO_FOO_EVENT, p_head);
}


void onetwotwo_bar(OnetwotwoMonitor* monitor) {
  switch (monitor->state[ONETWOTWO_SC1_SCENARIO]) {
    case ONETWOTWO_SC1_GEN0:
      monitor->state[ONETWOTWO_SC1_SCENARIO] = ONETWOTWO_SC1_ONETWO;
      break;

    default:
      raise_error("onetwotwo_sc1", onetwotwo_states_names[ONETWOTWO_SC1_SCENARIO][monitor->state[ONETWOTWO_SC1_SCENARIO]], "bar", "DEFAULT");
      break;
  }
}

void raise_onetwotwo_bar(OnetwotwoMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, ONETWOTWO_BAR_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_onetwotwo_monitor_maps() {
    if (pthread_mutex_init(&onetwotwo_monitor_maps_lock, NULL) != 0) {
        printf("\nOnetwotwo Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < ONETWOTWO_MONITOR_IDENTITIES; i++) {
        onetwotwo_monitor_maps[i] = (OnetwotwoMonitorMap*)malloc(sizeof(OnetwotwoMonitorMap));
    }
    return 1;
}

int add_onetwotwo_monitor_to_map(OnetwotwoMonitor *monitor, int identity) {
    OnetwotwoMonitorMap* map = onetwotwo_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, ONETWOTWO_MONITOR_MAP_SIZE);
    OnetwotwoMonitorRecord* record = (OnetwotwoMonitorRecord*)malloc(sizeof(OnetwotwoMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&onetwotwo_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&onetwotwo_monitor_maps_lock);
    return 1;
}

int put_onetwotwo_monitor(OnetwotwoMonitor *monitor) {
    return add_onetwotwo_monitor_to_map(monitor, ONETWOTWO_ID);
}

OnetwotwoMonitorRecord* get_onetwotwo_monitors() {
    OnetwotwoMonitorRecord* results = NULL;
    OnetwotwoMonitorMap* map = onetwotwo_monitor_maps[0];
    for(int i = 0; i < ONETWOTWO_MONITOR_MAP_SIZE; i++) {
        OnetwotwoMonitorRecord* current = map->list[i];
        while(current != NULL) {
            OnetwotwoMonitorRecord* record = (OnetwotwoMonitorRecord*)malloc(sizeof(OnetwotwoMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

OnetwotwoMonitorRecord* get_onetwotwo_monitors_by_identity(int identity, int type, void *value) {
    OnetwotwoMonitorRecord* results = NULL;
    OnetwotwoMonitorMap* map = onetwotwo_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, ONETWOTWO_MONITOR_MAP_SIZE);
    OnetwotwoMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            OnetwotwoMonitorRecord* record = (OnetwotwoMonitorRecord*)malloc(sizeof(OnetwotwoMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

OnetwotwoMonitorRecord* filter_onetwotwo_monitors_by_identity(OnetwotwoMonitorRecord* before, int identity, void  *value) {
    OnetwotwoMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            OnetwotwoMonitorRecord* record = (OnetwotwoMonitorRecord*)malloc(sizeof(OnetwotwoMonitorRecord));
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