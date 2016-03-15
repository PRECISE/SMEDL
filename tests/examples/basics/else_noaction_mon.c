//Compile: gcc -o else_noaction_mon -std=c99 actions.c monitor_map.c else_noaction_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "else_noaction_mon.h"

typedef enum { ELSENOACTION_ID } elsenoaction_identity;
const identity_type elsenoaction_identity_types[ELSENOACTION_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { ELSENOACTION_SC1_SCENARIO } elsenoaction_scenario;
typedef enum { ELSENOACTION_SC1_MIN1 } elsenoaction_sc1_state;
typedef enum { ELSENOACTION_FOO_EVENT } elsenoaction_event;
typedef enum { ELSENOACTION_DEFAULT } elsenoaction_error;
const char *elsenoaction_sc1_states[1] = {"Min1"};
const char **elsenoaction_states_names[1] = { elsenoaction_sc1_states };

ElsenoactionMonitor* init_elsenoaction_monitor( ElsenoactionData *d ) {
    ElsenoactionMonitor* monitor = (ElsenoactionMonitor*)malloc(sizeof(ElsenoactionMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[ELSENOACTION_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->bar = d->bar;
    monitor->state[ELSENOACTION_SC1_SCENARIO] = ELSENOACTION_SC1_MIN1;
    put_elsenoaction_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void elsenoaction_foo(ElsenoactionMonitor* monitor, int x) {
  switch (monitor->state[ELSENOACTION_SC1_SCENARIO]) {
    case ELSENOACTION_SC1_MIN1:
      if(monitor->bar == 1) {
        monitor->bar = x;
        monitor->state[ELSENOACTION_SC1_SCENARIO] = ELSENOACTION_SC1_MIN1;
      }
      else {
        monitor->state[ELSENOACTION_SC1_SCENARIO] = ELSENOACTION_SC1_MIN1;
      }
      break;

    default:
      raise_error("elsenoaction_sc1", elsenoaction_states_names[ELSENOACTION_SC1_SCENARIO][monitor->state[ELSENOACTION_SC1_SCENARIO]], "foo", "DEFAULT");
      break;
  }
}

void raise_elsenoaction_foo(ElsenoactionMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, ELSENOACTION_FOO_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_elsenoaction_monitor_maps() {
    if (pthread_mutex_init(&elsenoaction_monitor_maps_lock, NULL) != 0) {
        printf("\nElsenoaction Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < ELSENOACTION_MONITOR_IDENTITIES; i++) {
        elsenoaction_monitor_maps[i] = (ElsenoactionMonitorMap*)malloc(sizeof(ElsenoactionMonitorMap));
    }
    return 1;
}

int add_elsenoaction_monitor_to_map(ElsenoactionMonitor *monitor, int identity) {
    ElsenoactionMonitorMap* map = elsenoaction_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, ELSENOACTION_MONITOR_MAP_SIZE);
    ElsenoactionMonitorRecord* record = (ElsenoactionMonitorRecord*)malloc(sizeof(ElsenoactionMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&elsenoaction_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&elsenoaction_monitor_maps_lock);
    return 1;
}

int put_elsenoaction_monitor(ElsenoactionMonitor *monitor) {
    return add_elsenoaction_monitor_to_map(monitor, ELSENOACTION_ID);
}

ElsenoactionMonitorRecord* get_elsenoaction_monitors() {
    ElsenoactionMonitorRecord* results = NULL;
    ElsenoactionMonitorMap* map = elsenoaction_monitor_maps[0];
    for(int i = 0; i < ELSENOACTION_MONITOR_MAP_SIZE; i++) {
        ElsenoactionMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ElsenoactionMonitorRecord* record = (ElsenoactionMonitorRecord*)malloc(sizeof(ElsenoactionMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ElsenoactionMonitorRecord* get_elsenoaction_monitors_by_identity(int identity, int type, void *value) {
    ElsenoactionMonitorRecord* results = NULL;
    ElsenoactionMonitorMap* map = elsenoaction_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, ELSENOACTION_MONITOR_MAP_SIZE);
    ElsenoactionMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ElsenoactionMonitorRecord* record = (ElsenoactionMonitorRecord*)malloc(sizeof(ElsenoactionMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ElsenoactionMonitorRecord* filter_elsenoaction_monitors_by_identity(ElsenoactionMonitorRecord* before, int identity, void  *value) {
    ElsenoactionMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ElsenoactionMonitorRecord* record = (ElsenoactionMonitorRecord*)malloc(sizeof(ElsenoactionMonitorRecord));
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