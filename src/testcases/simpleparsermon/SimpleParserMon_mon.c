//Compile: gcc -o SimpleParserMon_mon -std=c99 actions.c monitor_map.c SimpleParserMon_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "SimpleParserMon_mon.h"

typedef enum { SIMPLEPARSERMON_ID } simpleparsermon_identity;
const identity_type simpleparsermon_identity_types[SIMPLEPARSERMON_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { SIMPLEPARSERMON_POINT_COUNTS_SCENARIO, SIMPLEPARSERMON_GETDISTANCE_SCENARIO, SIMPLEPARSERMON_GETSPEED_SCENARIO } simpleparsermon_scenario;
typedef enum { SIMPLEPARSERMON_POINT_COUNTS_ERROR, SIMPLEPARSERMON_POINT_COUNTS_READY, SIMPLEPARSERMON_POINT_COUNTS_GEN0, SIMPLEPARSERMON_POINT_COUNTS_GEN1 } simpleparsermon_point_counts_state;
typedef enum { SIMPLEPARSERMON_GETDISTANCE_ERROR, SIMPLEPARSERMON_GETDISTANCE_READY } simpleparsermon_getdistance_state;
typedef enum { SIMPLEPARSERMON_GETSPEED_ERROR, SIMPLEPARSERMON_GETSPEED_READY } simpleparsermon_getspeed_state;
typedef enum { SIMPLEPARSERMON_GETTIME_EVENT, SIMPLEPARSERMON_GETLON_EVENT, SIMPLEPARSERMON_GETSPEED_EVENT, SIMPLEPARSERMON_GETLAT_EVENT, SIMPLEPARSERMON_GETDIST_EVENT } simpleparsermon_event;
typedef enum { SIMPLEPARSERMON_DEFAULT } simpleparsermon_error;
const char *simpleparsermon_point_counts_states[4] = {"Error", "Ready", "Gen0", "Gen1"};
const char *simpleparsermon_getdistance_states[2] = {"Error", "Ready"};
const char *simpleparsermon_getspeed_states[2] = {"Error", "Ready"};
const char **simpleparsermon_states_names[3] = { simpleparsermon_point_counts_states, simpleparsermon_getdistance_states, simpleparsermon_getspeed_states };

SimpleparsermonMonitor* init_simpleparsermon_monitor( SimpleparsermonData *d ) {
    SimpleparsermonMonitor* monitor = (SimpleparsermonMonitor*)malloc(sizeof(SimpleparsermonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[SIMPLEPARSERMON_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->currentTime = d->currentTime;
    monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_ERROR;
    monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO] = SIMPLEPARSERMON_GETDISTANCE_ERROR;
    monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO] = SIMPLEPARSERMON_GETSPEED_ERROR;
    put_simpleparsermon_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]) {
    case SIMPLEPARSERMON_POINT_COUNTS_READY:
      if(time >= monitor->currentTime) {
        monitor->currentTime = time;
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_GEN0;
      }
      else {
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_ERROR;
      }
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO][monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]], "getTime", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE_SCENARIO][monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]], "getTime", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED_SCENARIO][monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]], "getTime", "DEFAULT");
      break;
  }
}

void simpleparsermon_getTime_probe(int time) {
  SimpleparsermonMonitorRecord* results = get_simpleparsermon_monitors();
  while(results != NULL) {
    SimpleparsermonMonitor* monitor = results->monitor;
    simpleparsermon_getTime(monitor, time);
    results = results->next;
  }
}

void raise_simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time) {
  param *p_head = NULL;
  push_param(&p_head, &time, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETTIME_EVENT, p_head);
}


void simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]) {
    case SIMPLEPARSERMON_POINT_COUNTS_GEN1:
      if(lon >= -180 && lon <= 180) {
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_READY;
      }
      else {
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_ERROR;
      }
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO][monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]], "getLon", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE_SCENARIO][monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]], "getLon", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED_SCENARIO][monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]], "getLon", "DEFAULT");
      break;
  }
}

void simpleparsermon_getLon_probe(float lon) {
  SimpleparsermonMonitorRecord* results = get_simpleparsermon_monitors();
  while(results != NULL) {
    SimpleparsermonMonitor* monitor = results->monitor;
    simpleparsermon_getLon(monitor, lon);
    results = results->next;
  }
}

void raise_simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETLON_EVENT, p_head);
}


void simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]) {
    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO][monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]], "getSpeed", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE_SCENARIO][monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]], "getSpeed", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]) {
    case SIMPLEPARSERMON_GETSPEED_READY:
      if(speed <= 6) {
        monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO] = SIMPLEPARSERMON_GETSPEED_READY;
      }
      else {
        monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO] = SIMPLEPARSERMON_GETSPEED_ERROR;
      }
      break;

    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED_SCENARIO][monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]], "getSpeed", "DEFAULT");
      break;
  }
}

void simpleparsermon_getSpeed_probe(float speed) {
  SimpleparsermonMonitorRecord* results = get_simpleparsermon_monitors();
  while(results != NULL) {
    SimpleparsermonMonitor* monitor = results->monitor;
    simpleparsermon_getSpeed(monitor, speed);
    results = results->next;
  }
}

void raise_simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETSPEED_EVENT, p_head);
}


void simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]) {
    case SIMPLEPARSERMON_POINT_COUNTS_GEN0:
      if(lat >= -90 && lat <= 90) {
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_GEN1;
      }
      else {
        monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO] = SIMPLEPARSERMON_POINT_COUNTS_ERROR;
      }
      break;

    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO][monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]], "getLat", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE_SCENARIO][monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]], "getLat", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED_SCENARIO][monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]], "getLat", "DEFAULT");
      break;
  }
}

void simpleparsermon_getLat_probe(float lat) {
  SimpleparsermonMonitorRecord* results = get_simpleparsermon_monitors();
  while(results != NULL) {
    SimpleparsermonMonitor* monitor = results->monitor;
    simpleparsermon_getLat(monitor, lat);
    results = results->next;
  }
}

void raise_simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETLAT_EVENT, p_head);
}


void simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist) {
  switch (monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]) {
    default:
      raise_error("simpleparsermon_point_counts", simpleparsermon_states_names[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO][monitor->state[SIMPLEPARSERMON_POINT_COUNTS_SCENARIO]], "getDist", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]) {
    case SIMPLEPARSERMON_GETDISTANCE_READY:
      if(dist >= 0) {
        monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO] = SIMPLEPARSERMON_GETDISTANCE_READY;
      }
      else {
        monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO] = SIMPLEPARSERMON_GETDISTANCE_ERROR;
      }
      break;

    default:
      raise_error("simpleparsermon_getDistance", simpleparsermon_states_names[SIMPLEPARSERMON_GETDISTANCE_SCENARIO][monitor->state[SIMPLEPARSERMON_GETDISTANCE_SCENARIO]], "getDist", "DEFAULT");
      break;
  }
  switch (monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]) {
    default:
      raise_error("simpleparsermon_getSpeed", simpleparsermon_states_names[SIMPLEPARSERMON_GETSPEED_SCENARIO][monitor->state[SIMPLEPARSERMON_GETSPEED_SCENARIO]], "getDist", "DEFAULT");
      break;
  }
}

void simpleparsermon_getDist_probe(float dist) {
  SimpleparsermonMonitorRecord* results = get_simpleparsermon_monitors();
  while(results != NULL) {
    SimpleparsermonMonitor* monitor = results->monitor;
    simpleparsermon_getDist(monitor, dist);
    results = results->next;
  }
}

void raise_simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SIMPLEPARSERMON_GETDIST_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

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

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}