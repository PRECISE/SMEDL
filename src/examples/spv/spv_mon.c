//Compile: gcc -o spv_mon -std=c99 actions.c monitor_map.c spv_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "spv_mon.h"

typedef enum { SPV_ID } spv_identity;
const identity_type spv_identity_types[SPV_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { SPV_PARSE_RECORD_SCENARIO, SPV_AFTER_END_SCENARIO } spv_scenario;
typedef enum { SPV_PARSE_RECORD_START } spv_parse_record_state;
typedef enum { SPV_AFTER_END_START, SPV_AFTER_END_END, SPV_AFTER_END_ERROR } spv_after_end_state;
typedef enum { SPV_PARSE_RECORD_EVENT, SPV_TIMESTEP_ERROR_EVENT } spv_event;
typedef enum { SPV_DEFAULT } spv_error;
const char *spv_parse_record_states[1] = { "Start" };
const char *spv_after_end_states[3] = { "Start", "End", "Error" };
const char **spv_states_names[2] = { spv_parse_record_states, spv_after_end_states };

SpvMonitor* init_spv_monitor( SpvData *d ) {
    SpvMonitor* monitor = (SpvMonitor*)malloc(sizeof(SpvMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[SPV_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->last_time = d->last_time;
    monitor->state[SPV_PARSE_RECORD_SCENARIO] = SPV_PARSE_RECORD_START;
    monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_START;
    put_spv_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void spv_parse_record(SpvMonitor* monitor, int time, float lat, float lon, int ret) {
  switch (monitor->state[SPV_PARSE_RECORD_SCENARIO]) {
    case SPV_PARSE_RECORD_START:
      if(time > monitor->last_time) {
        monitor->last_time = time;
        monitor->state[SPV_PARSE_RECORD_SCENARIO] = SPV_PARSE_RECORD_START;
      }
      else {
        ;
        monitor->state[SPV_PARSE_RECORD_SCENARIO] = SPV_PARSE_RECORD_START;
      }
      break;

    default:
      raise_error("spv_parse_record", spv_states_names[SPV_PARSE_RECORD_SCENARIO][monitor->state[SPV_PARSE_RECORD_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
  switch (monitor->state[SPV_AFTER_END_SCENARIO]) {
    case SPV_AFTER_END_END:
      monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_ERROR;
      break;

    case SPV_AFTER_END_START:
      if(ret == -1) {
        monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_END;
      }
      else {
        raise_error("after_end", spv_states_names[SPV_AFTER_END_SCENARIO][monitor->state[SPV_AFTER_END_SCENARIO]], "monitor->state[SPV_AFTER_END_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("spv_after_end", spv_states_names[SPV_AFTER_END_SCENARIO][monitor->state[SPV_AFTER_END_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
}

void raise_spv_parse_record(SpvMonitor* monitor, int time, float lat, float lon, int ret) {
  param *p_head = NULL;
  push_param(&p_head, &time, NULL, NULL, NULL);
  push_param(&p_head, &ret, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SPV_PARSE_RECORD_EVENT, p_head);
}


void spv_timestep_error(SpvMonitor* monitor, int time, int last_time) {
  switch (monitor->state[SPV_PARSE_RECORD_SCENARIO]) {
    default:
      raise_error("spv_parse_record", spv_states_names[SPV_PARSE_RECORD_SCENARIO][monitor->state[SPV_PARSE_RECORD_SCENARIO]], "timestep_error", "DEFAULT");
      break;
  }
  switch (monitor->state[SPV_AFTER_END_SCENARIO]) {
    default:
      raise_error("spv_after_end", spv_states_names[SPV_AFTER_END_SCENARIO][monitor->state[SPV_AFTER_END_SCENARIO]], "timestep_error", "DEFAULT");
      break;
  }
}

void raise_spv_timestep_error(SpvMonitor* monitor, int time, int last_time) {
  param *p_head = NULL;
  push_param(&p_head, &time, NULL, NULL, NULL);
  push_param(&p_head, &last_time, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SPV_TIMESTEP_ERROR_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_spv_monitor_maps() {
    if (pthread_mutex_init(&spv_monitor_maps_lock, NULL) != 0) {
        printf("\nSpv Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < SPV_MONITOR_IDENTITIES; i++) {
        spv_monitor_maps[i] = (SpvMonitorMap*)malloc(sizeof(SpvMonitorMap));
    }
    return 1;
}

int add_spv_monitor_to_map(SpvMonitor *monitor, int identity) {
    SpvMonitorMap* map = spv_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, SPV_MONITOR_MAP_SIZE);
    SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&spv_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&spv_monitor_maps_lock);
    return 1;
}

int put_spv_monitor(SpvMonitor *monitor) {
    return add_spv_monitor_to_map(monitor, SPV_ID);
}

SpvMonitorRecord* get_spv_monitors() {
    SpvMonitorRecord* results = NULL;
    SpvMonitorMap* map = spv_monitor_maps[0];
    for(int i = 0; i < SPV_MONITOR_MAP_SIZE; i++) {
        SpvMonitorRecord* current = map->list[i];
        while(current != NULL) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

SpvMonitorRecord* get_spv_monitors_by_identity(int identity, int type, void *value) {
    SpvMonitorRecord* results = NULL;
    SpvMonitorMap* map = spv_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, SPV_MONITOR_MAP_SIZE);
    SpvMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

SpvMonitorRecord* filter_spv_monitors_by_identity(SpvMonitorRecord* before, int identity, void  *value) {
    SpvMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
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