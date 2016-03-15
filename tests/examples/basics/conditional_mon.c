//Compile: gcc -o conditional_mon -std=c99 actions.c monitor_map.c conditional_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "conditional_mon.h"

typedef enum { CONDITIONAL_ID } conditional_identity;
const identity_type conditional_identity_types[CONDITIONAL_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { CONDITIONAL_SC1_SCENARIO } conditional_scenario;
typedef enum { CONDITIONAL_SC1_MIN1 } conditional_sc1_state;
typedef enum { CONDITIONAL_FOO_EVENT } conditional_event;
typedef enum { CONDITIONAL_DEFAULT } conditional_error;
const char *conditional_sc1_states[1] = {"Min1"};
const char **conditional_states_names[1] = { conditional_sc1_states };

ConditionalMonitor* init_conditional_monitor( ConditionalData *d ) {
    ConditionalMonitor* monitor = (ConditionalMonitor*)malloc(sizeof(ConditionalMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[CONDITIONAL_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->bar = d->bar;
    monitor->state[CONDITIONAL_SC1_SCENARIO] = CONDITIONAL_SC1_MIN1;
    put_conditional_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void conditional_foo(ConditionalMonitor* monitor, int x) {
  switch (monitor->state[CONDITIONAL_SC1_SCENARIO]) {
    case CONDITIONAL_SC1_MIN1:
      if(monitor->bar == 1) {
        monitor->state[CONDITIONAL_SC1_SCENARIO] = CONDITIONAL_SC1_MIN1;
      }
      else {
        raise_error("sc1", conditional_states_names[CONDITIONAL_SC1_SCENARIO][monitor->state[CONDITIONAL_SC1_SCENARIO]], "monitor->state[CONDITIONAL_SC1_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("conditional_sc1", conditional_states_names[CONDITIONAL_SC1_SCENARIO][monitor->state[CONDITIONAL_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_conditional_foo(ConditionalMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, CONDITIONAL_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_conditional_monitor_maps() {
    if (pthread_mutex_init(&conditional_monitor_maps_lock, NULL) != 0) {
        printf("\nConditional Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < CONDITIONAL_MONITOR_IDENTITIES; i++) {
        conditional_monitor_maps[i] = (ConditionalMonitorMap*)malloc(sizeof(ConditionalMonitorMap));
    }
    return 1;
}

int add_conditional_monitor_to_map(ConditionalMonitor *monitor, int identity) {
    ConditionalMonitorMap* map = conditional_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, CONDITIONAL_MONITOR_MAP_SIZE);
    ConditionalMonitorRecord* record = (ConditionalMonitorRecord*)malloc(sizeof(ConditionalMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&conditional_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&conditional_monitor_maps_lock);
    return 1;
}

int put_conditional_monitor(ConditionalMonitor *monitor) {
    return add_conditional_monitor_to_map(monitor, CONDITIONAL_ID);
}

ConditionalMonitorRecord* get_conditional_monitors() {
    ConditionalMonitorRecord* results = NULL;
    ConditionalMonitorMap* map = conditional_monitor_maps[0];
    for(int i = 0; i < CONDITIONAL_MONITOR_MAP_SIZE; i++) {
        ConditionalMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ConditionalMonitorRecord* record = (ConditionalMonitorRecord*)malloc(sizeof(ConditionalMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ConditionalMonitorRecord* get_conditional_monitors_by_identity(int identity, int type, void *value) {
    ConditionalMonitorRecord* results = NULL;
    ConditionalMonitorMap* map = conditional_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, CONDITIONAL_MONITOR_MAP_SIZE);
    ConditionalMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ConditionalMonitorRecord* record = (ConditionalMonitorRecord*)malloc(sizeof(ConditionalMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ConditionalMonitorRecord* filter_conditional_monitors_by_identity(ConditionalMonitorRecord* before, int identity, void  *value) {
    ConditionalMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ConditionalMonitorRecord* record = (ConditionalMonitorRecord*)malloc(sizeof(ConditionalMonitorRecord));
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