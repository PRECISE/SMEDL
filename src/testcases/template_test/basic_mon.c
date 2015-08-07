//Compile: gcc -o basic_mon -std=c99 actions.c monitor_map.c basic_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "basic_mon.h"

typedef enum { BASIC_NUM, BASIC_DATA} basic_identity;
const identity_type basic_identity_types[BASIC_MONITOR_IDENTITIES] = { INT, POINTER };

typedef enum { BASIC_MAIN, BASIC_TOTAL } basic_scenario;
typedef enum { BASIC_MAIN_X, BASIC_MAIN_Y } basic_main_state;
typedef enum { BASIC_TOTAL_STOP, BASIC_TOTAL_RUN } basic_total_state;
typedef enum { BASIC_UPY, BASIC_UPX, BASIC_UPTOTAL } basic_event;
typedef enum { BASIC_DEFAULT } basic_error;
const char *basic_main_states[2] = {"X", "Y"};
const char *basic_total_states[2] = {"Stop", "Run"};
const char **basic_states_names[2] = { basic_main_states, basic_total_states };

BasicMonitor* init_basic_monitor( BasicData *d ) {
    BasicMonitor* monitor = (BasicMonitor*)malloc(sizeof(BasicMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[BASIC_NUM] = init_monitor_identity(INT, &d->num);
    monitor->identities[BASIC_DATA] = init_monitor_identity(POINTER, d->data);
    monitor->y = d->y;
    monitor->x = d->x;
    monitor->total = d->total;
    monitor->state[BASIC_MAIN] = BASIC_MAIN_X;
    monitor->state[BASIC_TOTAL] = BASIC_TOTAL_STOP;  
    put_basic_monitor(monitor);
    return monitor;
}

int init_basic_monitor_maps() {
    if (pthread_mutex_init(&basic_monitor_maps_lock, NULL) != 0) {
        printf("\nBasic Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < BASIC_MONITOR_IDENTITIES; i++) {
        basic_monitor_maps[i] = (BasicMonitorMap*)malloc(sizeof(BasicMonitorMap));
    }
    return 1;
}

int add_basic_monitor_to_map(BasicMonitor *monitor, int identity) {
    BasicMonitorMap* map = basic_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type, 
        monitor->identities[identity]->value, BASIC_MONITOR_MAP_SIZE);
    BasicMonitorRecord* record = (BasicMonitorRecord*)malloc(sizeof(BasicMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&basic_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&basic_monitor_maps_lock);
    return 1; 
}

int put_basic_monitor(BasicMonitor *monitor) {
    return add_basic_monitor_to_map(monitor, BASIC_NUM) &&
      add_basic_monitor_to_map(monitor, BASIC_DATA);
}

BasicMonitorRecord* get_basic_monitors() {
    BasicMonitorRecord* results = NULL;
    BasicMonitorMap* map = basic_monitor_maps[0];
    for(int i = 0; i < BASIC_MONITOR_MAP_SIZE; i++) {
        BasicMonitorRecord* current = map->list[i];
        while(current != NULL) {
            BasicMonitorRecord* record = (BasicMonitorRecord*)malloc(sizeof(BasicMonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;  
            current = current->next;        
        }   
    }
    return results; 
}

BasicMonitorRecord* get_basic_monitors_by_identity(int identity, int type, void *value) {
    BasicMonitorRecord* results = NULL;
    BasicMonitorMap* map = basic_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, BASIC_MONITOR_MAP_SIZE);
    BasicMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            BasicMonitorRecord* record = (BasicMonitorRecord*)malloc(sizeof(BasicMonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;       
        }
        current = current->next;
    }
    return results;
}

BasicMonitorRecord* filter_basic_monitors_by_identity(BasicMonitorRecord* before, int identity, void  *value) {
    BasicMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            BasicMonitorRecord* record = (BasicMonitorRecord*)malloc(sizeof(BasicMonitorRecord)); 
            record->monitor = before->monitor;
            record->next = results;
            results = record;               
        }
        before = before->next;
    }
    return results;
}

void basic_upY(BasicMonitorRecord* monitor_list) {
  BasicMonitorRecord *current = monitor_list;
  while(current != NULL) {
    BasicMonitor* monitor = current->monitor;
    switch (monitor->state[BASIC_MAIN]) {
      case BASIC_MAIN_Y:
        monitor->state[BASIC_MAIN] = BASIC_MAIN_X;
        break;

      default:
        raise_error("basic_main", basic_states_names[BASIC_MAIN][monitor->state[BASIC_MAIN]], "upY", "DEFAULT");
        break;
    }
    switch (monitor->state[BASIC_TOTAL]) {
      default:
        raise_error("basic_total", basic_states_names[BASIC_TOTAL][monitor->state[BASIC_TOTAL]], "upY", "DEFAULT");
        break;
    }
    current = current->next;
  }
}

void raise_basic_upY(BasicMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, BASIC_UPY, p_head);
}


void basic_upX(BasicMonitorRecord* monitor_list) {
  BasicMonitorRecord *current = monitor_list;
  while(current != NULL) {
    BasicMonitor* monitor = current->monitor;
    switch (monitor->state[BASIC_MAIN]) {
      case BASIC_MAIN_X:
        monitor->state[BASIC_MAIN] = BASIC_MAIN_Y;
        break;

      default:
        raise_error("basic_main", basic_states_names[BASIC_MAIN][monitor->state[BASIC_MAIN]], "upX", "DEFAULT");
        break;
    }
    switch (monitor->state[BASIC_TOTAL]) {
      default:
        raise_error("basic_total", basic_states_names[BASIC_TOTAL][monitor->state[BASIC_TOTAL]], "upX", "DEFAULT");
        break;
    }
    current = current->next;
  }
}

void raise_basic_upX(BasicMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, BASIC_UPX, p_head);
}


void basic_upTotal(BasicMonitorRecord* monitor_list, int x) {
  BasicMonitorRecord *current = monitor_list;
  while(current != NULL) {
    BasicMonitor* monitor = current->monitor;
    switch (monitor->state[BASIC_MAIN]) {
      default:
        raise_error("basic_main", basic_states_names[BASIC_MAIN][monitor->state[BASIC_MAIN]], "upTotal", "DEFAULT");
        break;
    }
    switch (monitor->state[BASIC_TOTAL]) {
      case BASIC_TOTAL_RUN:
        if(monitor->total < 10) {
          monitor->state[BASIC_TOTAL] = BASIC_TOTAL_RUN;
        } else {
          monitor->state[BASIC_TOTAL] = BASIC_TOTAL_STOP;
        }
        break;

      default:
        raise_error("basic_total", basic_states_names[BASIC_TOTAL][monitor->state[BASIC_TOTAL]], "upTotal", "DEFAULT");
        break;
    }
    current = current->next;
  }
}

void raise_basic_upTotal(BasicMonitor* monitor, int x) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_action(&monitor->action_queue, BASIC_UPTOTAL, p_head);
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

