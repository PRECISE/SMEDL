//Compile: gcc -o pqueue_mon -std=c99 actions.c monitor_map.c pqueue_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "pqueue_mon.h"

typedef enum { PQUEUE_ID } pqueue_identity;
const identity_type pqueue_identity_types[PQUEUE_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { PQUEUE_PUSH_SCENARIO, PQUEUE_POP_SCENARIO } pqueue_scenario;
typedef enum { PQUEUE_PUSH_READY } pqueue_push_state;
typedef enum { PQUEUE_POP_ERROR, PQUEUE_POP_READY } pqueue_pop_state;
typedef enum { PQUEUE_PUSH, PQUEUE_POP } pqueue_event;
typedef enum { PQUEUE_DEFAULT } pqueue_error;
const char *pqueue_push_states[1] = {"Ready"};
const char *pqueue_pop_states[2] = {"Error", "Ready"};
const char **pqueue_states_names[2] = { pqueue_push_states, pqueue_pop_states };

PqueueMonitor* init_pqueue_monitor( PqueueData *d ) {
    PqueueMonitor* monitor = (PqueueMonitor*)malloc(sizeof(PqueueMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[PQUEUE_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->p4 = d->p4;
    monitor->p3 = d->p3;
    monitor->p5 = d->p5;
    monitor->p1 = d->p1;
    monitor->p2 = d->p2;
    monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
    monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
    put_pqueue_monitor(monitor);
    return monitor;
}

int init_pqueue_monitor_maps() {
    if (pthread_mutex_init(&pqueue_monitor_maps_lock, NULL) != 0) {
        printf("\nPqueue Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < PQUEUE_MONITOR_IDENTITIES; i++) {
        pqueue_monitor_maps[i] = (PqueueMonitorMap*)malloc(sizeof(PqueueMonitorMap));
    }
    return 1;
}

int add_pqueue_monitor_to_map(PqueueMonitor *monitor, int identity) {
    PqueueMonitorMap* map = pqueue_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, PQUEUE_MONITOR_MAP_SIZE);
    PqueueMonitorRecord* record = (PqueueMonitorRecord*)malloc(sizeof(PqueueMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&pqueue_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&pqueue_monitor_maps_lock);
    return 1;
}

int put_pqueue_monitor(PqueueMonitor *monitor) {
    return add_pqueue_monitor_to_map(monitor, PQUEUE_ID);
}

PqueueMonitorRecord* get_pqueue_monitors() {
    PqueueMonitorRecord* results = NULL;
    PqueueMonitorMap* map = pqueue_monitor_maps[0];
    for(int i = 0; i < PQUEUE_MONITOR_MAP_SIZE; i++) {
        PqueueMonitorRecord* current = map->list[i];
        while(current != NULL) {
            PqueueMonitorRecord* record = (PqueueMonitorRecord*)malloc(sizeof(PqueueMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

PqueueMonitorRecord* get_pqueue_monitors_by_identity(int identity, int type, void *value) {
    PqueueMonitorRecord* results = NULL;
    PqueueMonitorMap* map = pqueue_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, PQUEUE_MONITOR_MAP_SIZE);
    PqueueMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            PqueueMonitorRecord* record = (PqueueMonitorRecord*)malloc(sizeof(PqueueMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

PqueueMonitorRecord* filter_pqueue_monitors_by_identity(PqueueMonitorRecord* before, int identity, void  *value) {
    PqueueMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            PqueueMonitorRecord* record = (PqueueMonitorRecord*)malloc(sizeof(PqueueMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void pqueue_push(PqueueMonitor* monitor, int x) {
  switch (monitor->state[PQUEUE_PUSH]) {
    case PQUEUE_PUSH_READY:
      if(x == 1) {
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
      } else {
        raise_error("push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      }
      break;

    case PQUEUE_PUSH_READY:
      if(x == 2) {
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
      } else {
        raise_error("push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      }
      break;

    case PQUEUE_PUSH_READY:
      if(x == 3) {
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
      } else {
        raise_error("push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      }
      break;

    case PQUEUE_PUSH_READY:
      if(x == 4) {
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
      } else {
        raise_error("push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      }
      break;

    case PQUEUE_PUSH_READY:
      if(x == 5) {
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
      } else {
        raise_error("push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      }
      break;

    default:
      raise_error("pqueue_push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "push", "DEFAULT");
      break;
  }
  switch (monitor->state[PQUEUE_POP]) {
    default:
      raise_error("pqueue_pop", pqueue_states_names[PQUEUE_POP][monitor->state[PQUEUE_POP]], "push", "DEFAULT");
      break;
  }
}

void pqueue_push_probe(void* id) {
  PqueueMonitorRecord* results = get_pqueue_monitors_by_identity(PQUEUE_ID, OPAQUE, id);
  while(results != NULL) {
    PqueueMonitor* monitor = results->monitor;
    pqueue_push(monitor, x);
    results = results->next;
  }
}

void raise_pqueue_push(PqueueMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, PQUEUE_PUSH, p_head);
}


void pqueue_pop(PqueueMonitor* monitor, int x) {
  switch (monitor->state[PQUEUE_PUSH]) {
    default:
      raise_error("pqueue_push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "pop", "DEFAULT");
      break;
  }
  switch (monitor->state[PQUEUE_POP]) {
    case PQUEUE_POP_READY:
      if(x == 1 && monitor->p1 > 0) {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
      } else {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
      }
      break;

    case PQUEUE_POP_READY:
      if(x == 2 && monitor->p1 == 0 && monitor->p2 > 0) {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
      } else {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
      }
      break;

    case PQUEUE_POP_READY:
      if(x == 3 && monitor->p1 == 0 && monitor->p2 == 0 && monitor->p3 > 0) {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
      } else {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
      }
      break;

    case PQUEUE_POP_READY:
      if(x == 4 && monitor->p1 == 0 && monitor->p2 == 0 && monitor->p3 == 0 && monitor->p4 > 0) {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
      } else {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
      }
      break;

    case PQUEUE_POP_READY:
      if(x == 5 && monitor->p1 == 0 && monitor->p2 == 0 && monitor->p3 == 0 && monitor->p4 == 0 && monitor->p5 > 0) {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
      } else {
        monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
      }
      break;

    default:
      raise_error("pqueue_pop", pqueue_states_names[PQUEUE_POP][monitor->state[PQUEUE_POP]], "pop", "DEFAULT");
      break;
  }
}

void pqueue_pop_probe(void* id) {
  PqueueMonitorRecord* results = get_pqueue_monitors_by_identity(PQUEUE_ID, OPAQUE, id);
  while(results != NULL) {
    PqueueMonitor* monitor = results->monitor;
    pqueue_pop(monitor, x);
    results = results->next;
  }
}

void raise_pqueue_pop(PqueueMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, PQUEUE_POP, p_head);
}


void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

int main() { //To prevent warnings for test compile (they even happen with -c)
  return 0;
}

