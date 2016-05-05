//Compile: gcc -o explorer_mon -std=c99 actions.c monitor_map.c explorer_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "explorer_mon.h"

typedef enum { EXPLORER_ID } explorer_identity;
const identity_type explorer_identity_types[EXPLORER_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { EXPLORER_MAIN_SCENARIO, EXPLORER_EXPLORE_SCENARIO } explorer_scenario;
typedef enum { EXPLORER_MAIN_EXPLORE, EXPLORER_MAIN_RETRIEVE } explorer_main_state;
typedef enum { EXPLORER_EXPLORE_MOVE, EXPLORER_EXPLORE_LOOK } explorer_explore_state;
typedef enum { EXPLORER_VIEW_EVENT, EXPLORER_DRIVE_EVENT, EXPLORER_TURN_EVENT, EXPLORER_FOUND_EVENT, EXPLORER_RETRIEVED_EVENT } explorer_event;
typedef enum { EXPLORER_DEFAULT } explorer_error;
const char *explorer_main_states[2] = { "Explore", "Retrieve" };
const char *explorer_explore_states[2] = { "Move", "Look" };
const char **explorer_states_names[2] = { explorer_main_states, explorer_explore_states };

ExplorerMonitor* init_explorer_monitor( ExplorerData *d ) {
    ExplorerMonitor* monitor = (ExplorerMonitor*)malloc(sizeof(ExplorerMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EXPLORER_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->mon_x = d->mon_x;
    monitor->mon_y = d->mon_y;
    monitor->heading = d->heading;
    monitor->interest_threshold = d->interest_threshold;
    monitor->state[EXPLORER_MAIN_SCENARIO] = EXPLORER_MAIN_EXPLORE;
    monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_LOOK;
    monitor->logFile = fopen("ExplorerMonitor.log", "w");
    put_explorer_monitor(monitor);
    return monitor;
}

void free_monitor(ExplorerMonitor* monitor) {
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void explorer_view(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y) {
  switch (monitor->state[EXPLORER_EXPLORE_SCENARIO]) {
    case EXPLORER_EXPLORE_LOOK:
      if(contains_object(mon_var_x, mon_var_y)) {
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: found; Event parameters : "); }
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_MOVE;
      }
      else {
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_MOVE;
      }
      break;

  }
}

void raise_explorer_view(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_x, NULL, NULL, NULL);
  push_param(&p_head, &mon_var_y, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_VIEW_EVENT, p_head);
}


void explorer_drive(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y, int mon_var_heading) {
  switch (monitor->state[EXPLORER_EXPLORE_SCENARIO]) {
    case EXPLORER_EXPLORE_MOVE:
      if(mon_var_x == monitor->mon_x && mon_var_y == monitor->mon_y) {
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: retrieved; Event parameters : "); }
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_LOOK;
      }
      else {
        monitor->mon_x = mon_var_x;
        monitor->mon_y = mon_var_y;
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_LOOK;
      }
      break;

  }
}

void explorer_drive_probe(void* id, void* idint mon_var_x, int mon_var_y, int mon_var_heading) {
  ExplorerMonitorRecord* results = get_explorer_monitors_by_identity(EXPLORER_ID, OPAQUE, id);
  results = filter_explorer_monitors_by_identity(results, EXPLORER_ID, id);
  while(results != NULL) {
    ExplorerMonitor* monitor = results->monitor;
    explorer_drive(monitor, mon_var_x, mon_var_y, mon_var_heading);
    results = results->next;
  }
}

void raise_explorer_drive(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y, int mon_var_heading) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_x, NULL, NULL, NULL);
  push_param(&p_head, &mon_var_y, NULL, NULL, NULL);
  push_param(&p_head, &mon_var_heading, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_DRIVE_EVENT, p_head);
}


void explorer_turn(ExplorerMonitor* monitor, int mon_var_facing) {
  switch (monitor->state[EXPLORER_EXPLORE_SCENARIO]) {
    case EXPLORER_EXPLORE_MOVE:
      if(mon_var_facing != monitor->heading) {
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_LOOK;
      }
      else {
        monitor->state[EXPLORER_EXPLORE_SCENARIO] = EXPLORER_EXPLORE_MOVE;
      }
      break;

  }
}

void raise_explorer_turn(ExplorerMonitor* monitor, int mon_var_facing) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_facing, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_TURN_EVENT, p_head);
}


void explorer_found(ExplorerMonitor* monitor) {
  switch (monitor->state[EXPLORER_MAIN_SCENARIO]) {
    case EXPLORER_MAIN_EXPLORE:
      monitor->state[EXPLORER_MAIN_SCENARIO] = EXPLORER_MAIN_RETRIEVE;
      break;

  }
}

void raise_explorer_found(ExplorerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORER_FOUND_EVENT, p_head);
}




void raise_explorer_retrieved(ExplorerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORER_RETRIEVED_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_explorer_monitor_maps() {
    if (pthread_mutex_init(&explorer_monitor_maps_lock, NULL) != 0) {
        printf("\nExplorer Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < EXPLORER_MONITOR_IDENTITIES; i++) {
        explorer_monitor_maps[i] = (ExplorerMonitorMap*)malloc(sizeof(ExplorerMonitorMap));
    }
    return 1;
}

void free_explorer_monitor_maps() {
    // TODO
}

int add_explorer_monitor_to_map(ExplorerMonitor *monitor, int identity) {
    ExplorerMonitorMap* map = explorer_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, EXPLORER_MONITOR_MAP_SIZE);
    ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&explorer_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&explorer_monitor_maps_lock);
    return 1;
}

int put_explorer_monitor(ExplorerMonitor *monitor) {
    return add_explorer_monitor_to_map(monitor, EXPLORER_ID);
}

ExplorerMonitorRecord* get_explorer_monitors() {
    ExplorerMonitorRecord* results = NULL;
    ExplorerMonitorMap* map = explorer_monitor_maps[0];
    for(int i = 0; i < EXPLORER_MONITOR_MAP_SIZE; i++) {
        ExplorerMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ExplorerMonitorRecord* get_explorer_monitors_by_identity(int identity, int type, void *value) {
    ExplorerMonitorRecord* results = NULL;
    ExplorerMonitorMap* map = explorer_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, EXPLORER_MONITOR_MAP_SIZE);
    ExplorerMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ExplorerMonitorRecord* filter_explorer_monitors_by_identity(ExplorerMonitorRecord* before, int identity, void  *value) {
    ExplorerMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}\n", scen, state, action, type);
}