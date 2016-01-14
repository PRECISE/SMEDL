//Compile: gcc -o SimpleParseMon_mon -std=c99 actions.c monitor_map.c SimpleParseMon_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "SimpleParseMon_mon.h"

typedef enum { SIMPLEPARSERMON_ID } simpleparsermon_identity;
const identity_type simpleparsermon_identity_types[SIMPLEPARSERMON_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { SIMPLEPARSERMON_POINT_COUNTS_SCENARIO, SIMPLEPARSERMON_GETDISTANCE_SCENARIO, SIMPLEPARSERMON_GETSPEED_SCENARIO } simpleparsermon_scenario;
typedef enum { SIMPLEPARSERMON_POINT_COUNTS_ERROR, SIMPLEPARSERMON_POINT_COUNTS_READY, SIMPLEPARSERMON_POINT_COUNTS_GEN0, SIMPLEPARSERMON_POINT_COUNTS_GEN1 } simpleparsermon_point_counts_state;
typedef enum { SIMPLEPARSERMON_GETDISTANCE_ERROR, SIMPLEPARSERMON_GETDISTANCE_READY } simpleparsermon_getdistance_state;
typedef enum { SIMPLEPARSERMON_GETSPEED_ERROR, SIMPLEPARSERMON_GETSPEED_READY } simpleparsermon_getspeed_state;
typedef enum { SIMPLEPARSERMON_GETLAT, SIMPLEPARSERMON_GETSPEED, SIMPLEPARSERMON_GETTIME, SIMPLEPARSERMON_GETLON, SIMPLEPARSERMON_GETDIST } simpleparsermon_event;
typedef enum { SIMPLEPARSERMON_DEFAULT } simpleparsermon_error;
const char *simpleparsermon_point_counts_states[4] = {"Error", "Ready", "Gen0", "Gen1"};
const char *simpleparsermon_getdistance_states[2] = {"Error", "Ready"};
const char *simpleparsermon_getspeed_states[2] = {"Error", "Ready"};
const char **simpleparsermon_states_names[3] = { simpleparsermon_point_counts_states, simpleparsermon_getdistance_states, simpleparsermon_getspeed_states };

SimpleparsermonMonitor* init_simpleparsermon_monitor( SimpleparsermonData *d ) {
    SimpleparsermonMonitor* monitor = (SimpleparsermonMonitor*)malloc(sizeof(SimpleparsermonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[SIMPLEPARSERMON_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->currenttime = d->currenttime;
    monitor->state[SIMPLEPARSERMON_POINT_COUNTS] = SIMPLEPARSERMON_POINT_COUNTS_ERROR;
    monitor->state[SIMPLEPARSERMON_GETDISTANCE] = SIMPLEPARSERMON_GETDISTANCE_ERROR;
    monitor->state[SIMPLEPARSERMON_GETSPEED] = SIMPLEPARSERMON_GETSPEED_ERROR;
    put_simpleparsermon_monitor(monitor);
    return monitor;
}

int init_simpleparsermon_monitor_maps() {
    if (pthread_mutex_init(&simpleparsermon_monitor_maps_lock, NULL) != 0) {
        printf("\nSimpleparsermon Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < SIMPLEPARSERMON_MONITOR_IDENTITIES; i++) {
        simpleparsermon_monitor_maps[i] = (SimpleparsermonMonitorMap*)malloc(sizeof(SimpleparsermonMonitorMap));
    }
    return 1;
}

int add_simpleparsermon_monitor_to_map(SimpleparsermonMonitor *monitor, int identity) {
    SimpleparsermonMonitorMap* map = simpleparsermon_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, SIMPLEPARSERMON_MONITOR_MAP_SIZE);
    SimpleparsermonMonitorRecord* record = (SimpleparsermonMonitorRecord*)malloc(sizeof(SimpleparsermonMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&simpleparsermon_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&simpleparsermon_monitor_maps_lock);
    return 1;
}

int put_simpleparsermon_monitor(SimpleparsermonMonitor *monitor) {
    return add_simpleparsermon_monitor_to_map(monitor, SIMPLEPARSERMON_ID);
}

SimpleparsermonMonitorRecord* get_simpleparsermon_monitors() {
    SimpleparsermonMonitorRecord* results = NULL;
    SimpleparsermonMonitorMap* map = simpleparsermon_monitor_maps[0];
    for(int i = 0; i < SIMPLEPARSERMON_MONITOR_MAP_SIZE; i++) {
        SimpleparsermonMonitorRecord* current = map->list[i];
        while(current != NULL) {
            SimpleparsermonMonitorRecord* record = (SimpleparsermonMonitorRecord*)malloc(sizeof(SimpleparsermonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

SimpleparsermonMonitorRecord* get_simpleparsermon_monitors_by_identity(int identity, int type, void *value) {
    SimpleparsermonMonitorRecord* results = NULL;
    SimpleparsermonMonitorMap* map = simpleparsermon_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, SIMPLEPARSERMON_MONITOR_MAP_SIZE);
    SimpleparsermonMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            SimpleparsermonMonitorRecord* record = (SimpleparsermonMonitorRecord*)malloc(sizeof(SimpleparsermonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

SimpleparsermonMonitorRecord* filter_simpleparsermon_monitors_by_identity(SimpleparsermonMonitorRecord* before, int identity, void  *value) {
    SimpleparsermonMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            SimpleparsermonMonitorRecord* record = (SimpleparsermonMonitorRecord*)malloc(sizeof(SimpleparsermonMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS]) {
    case SIMPLEPARSERMON_POINT_COUNTS_GEN0:
      monitor->state[SIMPLEPARSERMON_POINT_COUNTS] = SIMPLEPARSERMON_POINT_COUNTS_GEN1;
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS][monitor->state[SIMPLEPARSERMON_POINT_COUNTS]], "getLat", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE][monitor->state[SIMPLEPARSERMON_GETDISTANCE]], "getLat", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED][monitor->state[SIMPLEPARSERMON_GETSPEED]], "getLat", "DEFAULT");
      break;
  }
}

void raise_simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETLAT, p_head);
}


void simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS]) {
    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS][monitor->state[SIMPLEPARSERMON_POINT_COUNTS]], "getSpeed", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE][monitor->state[SIMPLEPARSERMON_GETDISTANCE]], "getSpeed", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED]) {
    case SIMPLEPARSERMON_GETSPEED_READY:
      monitor->state[SIMPLEPARSERMON_GETSPEED] = SIMPLEPARSERMON_GETSPEED_READY;
      break;

    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED][monitor->state[SIMPLEPARSERMON_GETSPEED]], "getSpeed", "DEFAULT");
      break;
  }
}

void raise_simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETSPEED, p_head);
}


void simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS]) {
    case SIMPLEPARSERMON_POINT_COUNTS_READY:
      monitor->state[SIMPLEPARSERMON_POINT_COUNTS] = SIMPLEPARSERMON_POINT_COUNTS_GEN0;
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS][monitor->state[SIMPLEPARSERMON_POINT_COUNTS]], "getTime", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE][monitor->state[SIMPLEPARSERMON_GETDISTANCE]], "getTime", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED][monitor->state[SIMPLEPARSERMON_GETSPEED]], "getTime", "DEFAULT");
      break;
  }
}

void raise_simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time) {
  param *p_head = NULL;
  push_param(&p_head, &time, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETTIME, p_head);
}


void simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS]) {
    case SIMPLEPARSERMON_POINT_COUNTS_GEN1:
      monitor->state[SIMPLEPARSERMON_POINT_COUNTS] = SIMPLEPARSERMON_POINT_COUNTS_READY;
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS][monitor->state[SIMPLEPARSERMON_POINT_COUNTS]], "getLon", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE][monitor->state[SIMPLEPARSERMON_GETDISTANCE]], "getLon", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED][monitor->state[SIMPLEPARSERMON_GETSPEED]], "getLon", "DEFAULT");
      break;
  }
}

void raise_simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETLON, p_head);
}


void simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS]) {
    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS][monitor->state[SIMPLEPARSERMON_POINT_COUNTS]], "getDist", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE]) {
    case SIMPLEPARSERMON_GETDISTANCE_READY:
      monitor->state[SIMPLEPARSERMON_GETDISTANCE] = SIMPLEPARSERMON_GETDISTANCE_READY;
      break;

    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE][monitor->state[SIMPLEPARSERMON_GETDISTANCE]], "getDist", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED][monitor->state[SIMPLEPARSERMON_GETSPEED]], "getDist", "DEFAULT");
      break;
  }
}

void raise_simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETDIST, p_head);
}


void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

int main() { //To prevent warnings for test compile (they even happen with -c)
  return 0;
}

