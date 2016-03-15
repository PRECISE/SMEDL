//Compile: gcc -o action_update_mon -std=c99 actions.c monitor_map.c action_update_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "action_update_mon.h"

typedef enum {  } actup_identity;
const identity_type actup_identity_types[ACTUP_MONITOR_IDENTITIES] = {  };

typedef enum { ACTUP_SC1_SCENARIO } actup_scenario;
typedef enum { ACTUP_SC1_MIN1 } actup_sc1_state;
typedef enum { ACTUP_FOO_EVENT } actup_event;
typedef enum { ACTUP_DEFAULT } actup_error;
const char *actup_sc1_states[1] = {"Min1"};
const char **actup_states_names[1] = { actup_sc1_states };

ActupMonitor* init_actup_monitor( ActupData *d ) {
    ActupMonitor* monitor = (ActupMonitor*)malloc(sizeof(ActupMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->bar = d->bar;
    monitor->state[ACTUP_SC1_SCENARIO] = ACTUP_SC1_MIN1;
    put_actup_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void actup_foo(ActupMonitor* monitor, int x) {
  switch (monitor->state[ACTUP_SC1_SCENARIO]) {
    case ACTUP_SC1_MIN1:
      if(monitor->bar == 1) {
        monitor->bar = x;
        monitor->state[ACTUP_SC1_SCENARIO] = ACTUP_SC1_MIN1;
      }
      else {
        raise_error("sc1", actup_states_names[ACTUP_SC1_SCENARIO][monitor->state[ACTUP_SC1_SCENARIO]], "ActionType: State Update; Target: bar; Operator: =; Expression: AST({'trailer': None, 'unary': None, 'atom': 'x'})", "DEFAULT");
      }
      break;

    default:
      raise_error("actup_sc1", actup_states_names[ACTUP_SC1_SCENARIO][monitor->state[ACTUP_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_actup_foo(ActupMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, ACTUP_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_actup_monitor_maps() {
    if (pthread_mutex_init(&actup_monitor_maps_lock, NULL) != 0) {
        printf("\nActup Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < ACTUP_MONITOR_IDENTITIES; i++) {
        actup_monitor_maps[i] = (ActupMonitorMap*)malloc(sizeof(ActupMonitorMap));
    }
    return 1;
}

int add_actup_monitor_to_map(ActupMonitor *monitor, int identity) {
    ActupMonitorMap* map = actup_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, ACTUP_MONITOR_MAP_SIZE);
    ActupMonitorRecord* record = (ActupMonitorRecord*)malloc(sizeof(ActupMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&actup_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&actup_monitor_maps_lock);
    return 1;
}

int put_actup_monitor(ActupMonitor *monitor) {
    return ;
}

ActupMonitorRecord* get_actup_monitors() {
    ActupMonitorRecord* results = NULL;
    ActupMonitorMap* map = actup_monitor_maps[0];
    for(int i = 0; i < ACTUP_MONITOR_MAP_SIZE; i++) {
        ActupMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ActupMonitorRecord* record = (ActupMonitorRecord*)malloc(sizeof(ActupMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ActupMonitorRecord* get_actup_monitors_by_identity(int identity, int type, void *value) {
    ActupMonitorRecord* results = NULL;
    ActupMonitorMap* map = actup_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, ACTUP_MONITOR_MAP_SIZE);
    ActupMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ActupMonitorRecord* record = (ActupMonitorRecord*)malloc(sizeof(ActupMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ActupMonitorRecord* filter_actup_monitors_by_identity(ActupMonitorRecord* before, int identity, void  *value) {
    ActupMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ActupMonitorRecord* record = (ActupMonitorRecord*)malloc(sizeof(ActupMonitorRecord));
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