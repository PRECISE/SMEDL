//Compile: gcc -o state_mon -std=c99 actions.c monitor_map.c state_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "state_mon.h"

typedef enum { STATE_ID } state_identity;
const identity_type state_identity_types[STATE_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { STATE_SC1_SCENARIO } state_scenario;
typedef enum { STATE_SC1_MIN1 } state_sc1_state;
typedef enum { STATE_FOO_EVENT } state_event;
typedef enum { STATE_DEFAULT } state_error;
const char *state_sc1_states[1] = { "Min1" };
const char **state_states_names[1] = { state_sc1_states };

StateMonitor* init_state_monitor( StateData *d ) {
    StateMonitor* monitor = (StateMonitor*)malloc(sizeof(StateMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[STATE_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->bar = d->bar;
    monitor->state[STATE_SC1_SCENARIO] = STATE_SC1_MIN1;
    put_state_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void state_foo(StateMonitor* monitor, int x) {
  switch (monitor->state[STATE_SC1_SCENARIO]) {
    case STATE_SC1_MIN1:
      monitor->state[STATE_SC1_SCENARIO] = STATE_SC1_MIN1;
      break;

    default:
      raise_error("state_sc1", state_states_names[STATE_SC1_SCENARIO][monitor->state[STATE_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_state_foo(StateMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, STATE_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_state_monitor_maps() {
    if (pthread_mutex_init(&state_monitor_maps_lock, NULL) != 0) {
        printf("\nState Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < STATE_MONITOR_IDENTITIES; i++) {
        state_monitor_maps[i] = (StateMonitorMap*)malloc(sizeof(StateMonitorMap));
    }
    return 1;
}

int add_state_monitor_to_map(StateMonitor *monitor, int identity) {
    StateMonitorMap* map = state_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, STATE_MONITOR_MAP_SIZE);
    StateMonitorRecord* record = (StateMonitorRecord*)malloc(sizeof(StateMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&state_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&state_monitor_maps_lock);
    return 1;
}

int put_state_monitor(StateMonitor *monitor) {
    return add_state_monitor_to_map(monitor, STATE_ID);
}

StateMonitorRecord* get_state_monitors() {
    StateMonitorRecord* results = NULL;
    StateMonitorMap* map = state_monitor_maps[0];
    for(int i = 0; i < STATE_MONITOR_MAP_SIZE; i++) {
        StateMonitorRecord* current = map->list[i];
        while(current != NULL) {
            StateMonitorRecord* record = (StateMonitorRecord*)malloc(sizeof(StateMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

StateMonitorRecord* get_state_monitors_by_identity(int identity, int type, void *value) {
    StateMonitorRecord* results = NULL;
    StateMonitorMap* map = state_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, STATE_MONITOR_MAP_SIZE);
    StateMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            StateMonitorRecord* record = (StateMonitorRecord*)malloc(sizeof(StateMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

StateMonitorRecord* filter_state_monitors_by_identity(StateMonitorRecord* before, int identity, void  *value) {
    StateMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            StateMonitorRecord* record = (StateMonitorRecord*)malloc(sizeof(StateMonitorRecord));
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