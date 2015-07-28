//Compile: gcc -o explorer_mon -std=c99 actions.c monitor_map.c explorer_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "explorer_mon.h"
#include "helper.h"

typedef enum { EXPLORER_THR_ID, EXPLORER_FIRST_ID, EXPLORER_THING_PTR, EXPLORER_SECOND_ID} explorer_identity;
const identity_type explorer_identity_types[EXPLORER_MONITOR_IDENTITIES] = { THREAD, INT, POINTER, INT };

typedef enum { EXPLORER_MAIN, EXPLORER_EXPLORE } explorer_scenario;
typedef enum { EXPLORER_MAIN_EXPLORE, EXPLORER_MAIN_RETRIEVE } explorer_main_state;
typedef enum { EXPLORER_EXPLORE_MOVE, EXPLORER_EXPLORE_LOOK } explorer_explore_state;
typedef enum { EXPLORER_DRIVE, EXPLORER_TURN, EXPLORER_VIEW, EXPLORER_FOUND, EXPLORER_RETRIEVED } explorer_event;
typedef enum { EXPLORER_DEFAULT } explorer_error;
const char *explorer_main_states[2] = {"Explore", "Retrieve"};
const char *explorer_explore_states[2] = {"Move", "Look"};
const char **explorer_states_names[2] = { explorer_main_states, explorer_explore_states };

ExplorerMonitor* init_explorer_monitor( ExplorerData *d ) {
    ExplorerMonitor* monitor = (ExplorerMonitor*)malloc(sizeof(ExplorerMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EXPLORER_THR_ID] = init_monitor_identity(THREAD, d->thr_id);
    monitor->identities[EXPLORER_FIRST_ID] = init_monitor_identity(INT, &d->first_id);
    monitor->identities[EXPLORER_THING_PTR] = init_monitor_identity(POINTER, d->thing_ptr);
    monitor->identities[EXPLORER_SECOND_ID] = init_monitor_identity(INT, &d->second_id);
    monitor->explorer_view = d->explorer_view;
    monitor->x = d->x;
    monitor->interest_threshold = d->interest_threshold;
    monitor->y = d->y;
    monitor->heading = d->heading;
    monitor->state[EXPLORER_MAIN] = EXPLORER_MAIN_EXPLORE;
    monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_MOVE;  
    put_explorer_monitor(monitor);
    return monitor;
}

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
    return add_explorer_monitor_to_map(monitor, EXPLORER_THR_ID) &&
      add_explorer_monitor_to_map(monitor, EXPLORER_FIRST_ID) &&
      add_explorer_monitor_to_map(monitor, EXPLORER_THING_PTR) &&
      add_explorer_monitor_to_map(monitor, EXPLORER_SECOND_ID);
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

void drive(ExplorerMonitor* monitor, int x, int y, int heading) {
  switch (monitor->state[EXPLORER_MAIN]) {
    default:
      raise_error("explorer_main", explorer_states_names[EXPLORER_MAIN][monitor->state[EXPLORER_MAIN]], "drive", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORER_EXPLORE]) {
    case EXPLORER_EXPLORE_MOVE:
      if(x == monitor->x && y == monitor->y) {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_LOOK;
      } else {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_LOOK;
      }
      break;

    default:
      raise_error("explorer_explore", explorer_states_names[EXPLORER_EXPLORE][monitor->state[EXPLORER_EXPLORE]], "drive", "DEFAULT");
      break;
  }
}

void raise_drive(ExplorerMonitor* monitor, int x, int y, int heading) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_param(&p_head, &heading, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_DRIVE, p_head);
}


void turn(ExplorerMonitor* monitor, int facing) {
  switch (monitor->state[EXPLORER_MAIN]) {
    default:
      raise_error("explorer_main", explorer_states_names[EXPLORER_MAIN][monitor->state[EXPLORER_MAIN]], "turn", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORER_EXPLORE]) {
    case EXPLORER_EXPLORE_MOVE:
      if(facing != monitor->heading) {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_LOOK;
      } else {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_MOVE;
      }
      break;

    default:
      raise_error("explorer_explore", explorer_states_names[EXPLORER_EXPLORE][monitor->state[EXPLORER_EXPLORE]], "turn", "DEFAULT");
      break;
  }
}

void raise_turn(ExplorerMonitor* monitor, int facing) {
  param *p_head = NULL;
  push_param(&p_head, &facing, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_TURN, p_head);
}


void view(ExplorerMonitor* monitor, int x, int y) {
  switch (monitor->state[EXPLORER_MAIN]) {
    default:
      raise_error("explorer_main", explorer_states_names[EXPLORER_MAIN][monitor->state[EXPLORER_MAIN]], "view", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORER_EXPLORE]) {
    case EXPLORER_EXPLORE_LOOK:
      if(contains_object(monitor)) {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_MOVE;
      } else {
        monitor->state[EXPLORER_EXPLORE] = EXPLORER_EXPLORE_MOVE;
      }
      break;

    default:
      raise_error("explorer_explore", explorer_states_names[EXPLORER_EXPLORE][monitor->state[EXPLORER_EXPLORE]], "view", "DEFAULT");
      break;
  }
}

void raise_view(ExplorerMonitor* monitor, int x, int y) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_VIEW, p_head);
}


void found(ExplorerMonitor* monitor) {
  switch (monitor->state[EXPLORER_MAIN]) {
    case EXPLORER_MAIN_EXPLORE:
      monitor->state[EXPLORER_MAIN] = EXPLORER_MAIN_RETRIEVE;
      break;

    default:
      raise_error("explorer_main", explorer_states_names[EXPLORER_MAIN][monitor->state[EXPLORER_MAIN]], "found", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORER_EXPLORE]) {
    default:
      raise_error("explorer_explore", explorer_states_names[EXPLORER_EXPLORE][monitor->state[EXPLORER_EXPLORE]], "found", "DEFAULT");
      break;
  }
}

void raise_found(ExplorerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORER_FOUND, p_head);
}


void retrieved(ExplorerMonitor* monitor) {
  switch (monitor->state[EXPLORER_MAIN]) {
    case EXPLORER_MAIN_RETRIEVE:
      monitor->state[EXPLORER_MAIN] = EXPLORER_MAIN_EXPLORE;
      break;

    default:
      raise_error("explorer_main", explorer_states_names[EXPLORER_MAIN][monitor->state[EXPLORER_MAIN]], "retrieved", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORER_EXPLORE]) {
    default:
      raise_error("explorer_explore", explorer_states_names[EXPLORER_EXPLORE][monitor->state[EXPLORER_EXPLORE]], "retrieved", "DEFAULT");
      break;
  }
}

void raise_retrieved(ExplorerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORER_RETRIEVED, p_head);
}


void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

int main() { //To prevent warnings for test compile (they even happen with -c)
  return 0;
}

// TODO add back original smedlgen stuff:

// void drive(_Explorer* monitor, int x, int y, int heading) {
//   monitor->x = x;
//   monitor->y = y;
//   monitor->heading = heading;
//   // switch (monitor->state[MAIN]) {
//   //   default:
//   //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "drive", "DEFAULT");
//   //     break;
//   // }
//   // switch (monitor->state[EXPLORE]) {
//   //   case MOVE_EXPLORE:
//   //     if(x == monitor->x && y == monitor->y) {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     } else {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     }
//   //     break;
//   //   default:
//   //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
//   //     break;
//   // }
// }

// void raise_drive(_Explorer* monitor, int x, int y, int heading) {
//   param *p_head = NULL;
//   push_param(&p_head, &x, NULL, NULL, NULL);
//   push_param(&p_head, &y, NULL, NULL, NULL);
//   push_param(&p_head, &heading, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, DRIVE, p_head);
// }

// void turn(_Explorer* monitor, int facing) {
//   monitor->heading = facing;
//   // switch (monitor->state[MAIN]) {
//   //   default:
//   //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "turn", "DEFAULT");
//   //     break;
//   // }
//   // switch (monitor->state[EXPLORE]) {
//   //   case MOVE_EXPLORE:
//   //     if(facing != monitor->heading) {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     } else {
//   //       monitor->state[EXPLORE] = MOVE_EXPLORE;
//   //     }
//   //     break;
//   //   default:
//   //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
//   //     break;
//   // }
// }

// void raise_turn(_Explorer* monitor, int facing) {
//   param *p_head = NULL;
//   push_param(&p_head, &facing, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, TURN, p_head);
// }

// void scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) { //changed params from smedl
//   monitor->x = x;
//   monitor->y = y;
//   monitor->heading = heading;
//   set_view(monitor, map); //This raise needs to be immediate, not in queue
//   switch (monitor->state[MAIN]) {
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "view", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     case LOOK_EXPLORE:
//       if(contains_object(monitor)) {
//         raise_found(monitor);
//         monitor->state[EXPLORE] = MOVE_EXPLORE;
//       } else {
//         monitor->state[EXPLORE] = MOVE_EXPLORE;
//       }
//       break;
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
//       break;
//   }
// }

// void raise_scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) {
//   param *p_head = NULL;
//   push_param(&p_head, &x, NULL, NULL, NULL);
//   push_param(&p_head, &y, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, SCAN_VIEW, p_head);
// }

// void found(_Explorer* monitor) {
//   switch (monitor->state[MAIN]) {
//     case EXPLORE_MAIN:
//       monitor->state[MAIN] = RETRIEVE_MAIN;
//       break;
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "found", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "found", "DEFAULT");
//       break;
//   }
// }

// void raise_found(_Explorer* monitor) {
//   param *p_head = NULL;
//   push_action(&monitor->action_queue, FOUND, p_head);
// }

// void retrieved(_Explorer* monitor) {
//   switch (monitor->state[MAIN]) {
//     case RETRIEVE_MAIN:
//       monitor->state[MAIN] = EXPLORE_MAIN;
//       break;
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "retrieved", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "retrieved", "DEFAULT");
//       break;
//   }
// }

// void raise_retrieved(_Explorer* monitor) {
//   param *p_head = NULL;
//   push_action(&monitor->action_queue, RETRIEVED, p_head);
// }

// void call_next_action(_Explorer *monitor) {
//   switch (monitor->action_queue->id) {
//     case DRIVE: ;
//       int x_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int y_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int heading_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       drive(monitor, x_drive, y_drive, heading_drive);
//       break;
//     case TURN: ;
//       int facing_turn = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       turn(monitor, facing_turn);
//       break;
//     case SCAN_VIEW: ;
//       int x_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int y_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int heading_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       const void *map_view = monitor->action_queue->params->v;
//       pop_param(&monitor->action_queue->params);
//       scan_view(monitor, x_view, y_view, heading_view, map_view);
//       break;
//     case FOUND: ;
//       found(monitor);
//       break;
//     case RETRIEVED: ;
//       retrieved(monitor);
//       break;
//   }
// }

// void exec_actions(_Explorer *monitor) {
//   while(monitor->action_queue != NULL) {
//     call_next_action(monitor);
//     pop_action(&monitor->action_queue);
//   }
// }

// void raise_error(char *scen, const char *state, char *action, char *type) {
//   printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
// }

