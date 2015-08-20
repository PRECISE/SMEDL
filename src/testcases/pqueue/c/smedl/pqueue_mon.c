//Compile: gcc -o pqueue_mon -std=c99 actions.c monitor_map.c pqueue_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "pqueue_mon.h"

typedef enum { PQUEUE_ID} pqueue_identity;
const identity_type pqueue_identity_types[PQUEUE_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { PQUEUE_PUSH, PQUEUE_POP } pqueue_scenario;
typedef enum { PQUEUE_PUSH_READY } pqueue_push_state;
typedef enum { PQUEUE_POP_ERROR, PQUEUE_POP_READY } pqueue_pop_state;
typedef enum { PQUEUE_POP, PQUEUE_PUSH } pqueue_event;
typedef enum { PQUEUE_DEFAULT } pqueue_error;
const char *pqueue_push_states[1] = {"Ready"};
const char *pqueue_pop_states[2] = {"Error", "Ready"};
const char **pqueue_states_names[2] = { pqueue_push_states, pqueue_pop_states };

PqueueMonitor* init_pqueue_monitor( PqueueData *d ) {
    PqueueMonitor* monitor = (PqueueMonitor*)malloc(sizeof(PqueueMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[PQUEUE_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->p3 = d->p3;
    monitor->p5 = d->p5;
    monitor->p2 = d->p2;
    monitor->p1 = d->p1;
    monitor->p4 = d->p4;
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

void pqueue_pop(PqueueMonitorRecord* monitor_list, int 5) {
  PqueueMonitorRecord *current = monitor_list;
  while(current != NULL) {
    PqueueMonitor* monitor = current->monitor;
    switch (monitor->state[PQUEUE_PUSH]) {
      default:
        raise_error("pqueue_push", pqueue_states_names[PQUEUE_PUSH][monitor->state[PQUEUE_PUSH]], "pop", "DEFAULT");
        break;
    }
    switch (monitor->state[PQUEUE_POP]) {
      case PQUEUE_POP_READY:
        if(p1 > 0) {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
        } else {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
        }
        break;

      case PQUEUE_POP_READY:
        if(p1 == 0 && p2 > 0) {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
        } else {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
        }
        break;

      case PQUEUE_POP_READY:
        if(p1 == 0 && p2 == 0 && p3 > 0) {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
        } else {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
        }
        break;

      case PQUEUE_POP_READY:
        if(p1 == 0 && p2 == 0 && p3 == 0 && p4 > 0) {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
        } else {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
        }
        break;

      case PQUEUE_POP_READY:
        if(p1 == 0 && p2 == 0 && p3 == 0 && p4 == 0 && p5 > 0) {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_READY;
        } else {
          monitor->state[PQUEUE_POP] = PQUEUE_POP_ERROR;
        }
        break;

      default:
        raise_error("pqueue_pop", pqueue_states_names[PQUEUE_POP][monitor->state[PQUEUE_POP]], "pop", "DEFAULT");
        break;
    }
    current = current->next;
  }
}

void raise_pqueue_pop(PqueueMonitor* monitor, int 5) {
  param *p_head = NULL;
  push_param(&p_head, &5, NULL, NULL, NULL);
  push_action(&monitor->action_queue, PQUEUE_POP, p_head);
}


void pqueue_push(PqueueMonitorRecord* monitor_list, int 5) {
  PqueueMonitorRecord *current = monitor_list;
  while(current != NULL) {
    PqueueMonitor* monitor = current->monitor;
    switch (monitor->state[PQUEUE_PUSH]) {
      case PQUEUE_PUSH_READY:
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
        break;

      case PQUEUE_PUSH_READY:
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
        break;

      case PQUEUE_PUSH_READY:
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
        break;

      case PQUEUE_PUSH_READY:
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
        break;

      case PQUEUE_PUSH_READY:
        monitor->state[PQUEUE_PUSH] = PQUEUE_PUSH_READY;
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
    current = current->next;
  }
}

void raise_pqueue_push(PqueueMonitor* monitor, int 5) {
  param *p_head = NULL;
  push_param(&p_head, &5, NULL, NULL, NULL);
  push_action(&monitor->action_queue, PQUEUE_PUSH, p_head);
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

