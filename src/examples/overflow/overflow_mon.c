//Compile: gcc -o overflow_mon -std=c99 actions.c monitor_map.c overflow_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "overflow_mon.h"

typedef enum { OVFMON_BUFFER } ovfmon_identity;
const identity_type ovfmon_identity_types[OVFMON_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { OVFMON_BUFACCESS_SCENARIO } ovfmon_scenario;
typedef enum { OVFMON_BUFACCESS_INIT, OVFMON_BUFACCESS_READY } ovfmon_bufaccess_state;
typedef enum { OVFMON_REINIT_EVENT, OVFMON_WRITE_EVENT } ovfmon_event;
typedef enum { OVFMON_DEFAULT } ovfmon_error;
const char *ovfmon_bufaccess_states[2] = { "Init", "Ready" };
const char **ovfmon_states_names[1] = { ovfmon_bufaccess_states };

OvfmonMonitor* init_ovfmon_monitor( OvfmonData *d ) {
    OvfmonMonitor* monitor = (OvfmonMonitor*)malloc(sizeof(OvfmonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[OVFMON_BUFFER] = init_monitor_identity(OPAQUE, d->buffer);
    monitor->size = d->size;
    monitor->state[OVFMON_BUFACCESS_SCENARIO] = OVFMON_BUFACCESS_INIT;
    put_ovfmon_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void ovfmon_reinit(OvfmonMonitor* monitor, int new_siz) {
  switch (monitor->state[OVFMON_BUFACCESS_SCENARIO]) {
    case OVFMON_BUFACCESS_READY:
        monitor->size = new_siz;
      monitor->state[OVFMON_BUFACCESS_SCENARIO] = OVFMON_BUFACCESS_READY;
      break;

    case OVFMON_BUFACCESS_INIT:
        monitor->size = new_siz;
      monitor->state[OVFMON_BUFACCESS_SCENARIO] = OVFMON_BUFACCESS_READY;
      break;

    default:
      raise_error("ovfmon_bufaccess", ovfmon_states_names[OVFMON_BUFACCESS_SCENARIO][monitor->state[OVFMON_BUFACCESS_SCENARIO]], "reinit", "DEFAULT");
      break;
  }
}

void raise_ovfmon_reinit(OvfmonMonitor* monitor, int new_siz) {
  param *p_head = NULL;
  push_param(&p_head, &new_siz, NULL, NULL, NULL);
  push_action(&monitor->action_queue, OVFMON_REINIT_EVENT, p_head);
}


void ovfmon_write(OvfmonMonitor* monitor, int wsiz) {
  switch (monitor->state[OVFMON_BUFACCESS_SCENARIO]) {
    case OVFMON_BUFACCESS_READY:
      if(wsiz <= monitor->size) {
        monitor->state[OVFMON_BUFACCESS_SCENARIO] = OVFMON_BUFACCESS_READY;
      }
      else {
        raise_error("bufaccess", ovfmon_states_names[OVFMON_BUFACCESS_SCENARIO][monitor->state[OVFMON_BUFACCESS_SCENARIO]], "monitor->state[OVFMON_BUFACCESS_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("ovfmon_bufaccess", ovfmon_states_names[OVFMON_BUFACCESS_SCENARIO][monitor->state[OVFMON_BUFACCESS_SCENARIO]], "write", "DEFAULT");
      break;
  }
}

void raise_ovfmon_write(OvfmonMonitor* monitor, int wsiz) {
  param *p_head = NULL;
  push_param(&p_head, &wsiz, NULL, NULL, NULL);
  push_action(&monitor->action_queue, OVFMON_WRITE_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_ovfmon_monitor_maps() {
    if (pthread_mutex_init(&ovfmon_monitor_maps_lock, NULL) != 0) {
        printf("\nOvfmon Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < OVFMON_MONITOR_IDENTITIES; i++) {
        ovfmon_monitor_maps[i] = (OvfmonMonitorMap*)malloc(sizeof(OvfmonMonitorMap));
    }
    return 1;
}

int add_ovfmon_monitor_to_map(OvfmonMonitor *monitor, int identity) {
    OvfmonMonitorMap* map = ovfmon_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, OVFMON_MONITOR_MAP_SIZE);
    OvfmonMonitorRecord* record = (OvfmonMonitorRecord*)malloc(sizeof(OvfmonMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&ovfmon_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&ovfmon_monitor_maps_lock);
    return 1;
}

int put_ovfmon_monitor(OvfmonMonitor *monitor) {
    return add_ovfmon_monitor_to_map(monitor, OVFMON_BUFFER);
}

OvfmonMonitorRecord* get_ovfmon_monitors() {
    OvfmonMonitorRecord* results = NULL;
    OvfmonMonitorMap* map = ovfmon_monitor_maps[0];
    for(int i = 0; i < OVFMON_MONITOR_MAP_SIZE; i++) {
        OvfmonMonitorRecord* current = map->list[i];
        while(current != NULL) {
            OvfmonMonitorRecord* record = (OvfmonMonitorRecord*)malloc(sizeof(OvfmonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

OvfmonMonitorRecord* get_ovfmon_monitors_by_identity(int identity, int type, void *value) {
    OvfmonMonitorRecord* results = NULL;
    OvfmonMonitorMap* map = ovfmon_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, OVFMON_MONITOR_MAP_SIZE);
    OvfmonMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            OvfmonMonitorRecord* record = (OvfmonMonitorRecord*)malloc(sizeof(OvfmonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

OvfmonMonitorRecord* filter_ovfmon_monitors_by_identity(OvfmonMonitorRecord* before, int identity, void  *value) {
    OvfmonMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            OvfmonMonitorRecord* record = (OvfmonMonitorRecord*)malloc(sizeof(OvfmonMonitorRecord));
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