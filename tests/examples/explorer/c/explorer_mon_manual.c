#include <stdlib.h>
#include <stdio.h>
#include "actions.h"
#include "explorer_mon.h"
#include "helper.h"

typedef enum { MAIN, EXPLORE } scenario;
typedef enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_state;
typedef enum { MOVE_EXPLORE, LOOK_EXPLORE } explore_state;
typedef enum { DRIVE, TURN, SCAN_VIEW, FOUND, RETRIEVED } event; //Changed all VIEW and view() to SCAN_VIEW, scan_view()
typedef enum { DEFAULT } error_type;
const char *explorer_main_states[2] = {"Explore", "Retrieve"};
const char *explorer_explore_states[2] = {"Move", "Look"};
const char **explorer_states_names[2] = {explorer_main_states, explorer_explore_states};

_Explorer* init_Explorer(ExplorerData* d) {
  _Explorer* monitor = (_Explorer*)malloc(sizeof(_Explorer));
  monitor->id = d;
  monitor->y = d->y;
  monitor-> x = d->x;
  monitor->heading = d->heading;
  monitor->state[0] = EXPLORE_MAIN;
  monitor->state[1] = MOVE_EXPLORE;
  return monitor;
}

void free_Explorer(_Explorer* monitor) {
  free(monitor);
  return;
}

void init_checker_storage() {
  checkStore = NULL;
}

void free_checker_storage() { 
  while(checkStore != NULL) {
    CheckerRecord* temp = checkStore;
    checkStore = temp->next;
    free_Explorer(temp->checker);
    free(temp);   
  }
}

void add_checker(_Explorer* c) {
  CheckerRecord* tmp = checkStore;
  checkStore = (CheckerRecord*)malloc(sizeof(CheckerRecord));
  checkStore->checker = c;
  checkStore->next = tmp;
}

_Explorer* get_checker(const ExplorerData* key) {
  CheckerRecord* iter = checkStore;
  while (iter != NULL) {
    if (iter->checker->id == key) 
       break;
    iter = iter->next;
  }
  return iter->checker;
}

void drive(_Explorer* monitor, int x, int y, int heading) {
  monitor->x = x;
  monitor->y = y;
  monitor->heading = heading;
  // switch (monitor->state[MAIN]) {
  //   default:
  //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "drive", "DEFAULT");
  //     break;
  // }
  // switch (monitor->state[EXPLORE]) {
  //   case MOVE_EXPLORE:
  //     if(x == monitor->x && y == monitor->y) {
  //       monitor->state[EXPLORE] = LOOK_EXPLORE;
  //     } else {
  //       monitor->state[EXPLORE] = LOOK_EXPLORE;
  //     }
  //     break;
  //   default:
  //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
  //     break;
  // }
}

void raise_drive(_Explorer* monitor, int x, int y, int heading) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_param(&p_head, &heading, NULL, NULL, NULL);
  push_action(&monitor->action_queue, DRIVE, p_head);
}

void turn(_Explorer* monitor, int facing) {
  monitor->heading = facing;
  // switch (monitor->state[MAIN]) {
  //   default:
  //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "turn", "DEFAULT");
  //     break;
  // }
  // switch (monitor->state[EXPLORE]) {
  //   case MOVE_EXPLORE:
  //     if(facing != monitor->heading) {
  //       monitor->state[EXPLORE] = LOOK_EXPLORE;
  //     } else {
  //       monitor->state[EXPLORE] = MOVE_EXPLORE;
  //     }
  //     break;
  //   default:
  //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
  //     break;
  // }
}

void raise_turn(_Explorer* monitor, int facing) {
  param *p_head = NULL;
  push_param(&p_head, &facing, NULL, NULL, NULL);
  push_action(&monitor->action_queue, TURN, p_head);
}

void scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) { //changed params from smedl
  monitor->x = x;
  monitor->y = y;
  monitor->heading = heading;
  set_view(monitor, map); //This raise needs to be immediate, not in queue
  switch (monitor->state[MAIN]) {
    default:
      raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "view", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case LOOK_EXPLORE:
      if(contains_object(monitor)) {
        raise_found(monitor);
        monitor->state[EXPLORE] = MOVE_EXPLORE;
      } else {
        monitor->state[EXPLORE] = MOVE_EXPLORE;
      }
      break;
    default:
      raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      break;
  }
}

void raise_scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SCAN_VIEW, p_head);
}

void found(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case EXPLORE_MAIN:
      monitor->state[MAIN] = RETRIEVE_MAIN;
      break;
    default:
      raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "found", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "found", "DEFAULT");
      break;
  }
}

void raise_found(_Explorer* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, FOUND, p_head);
}

void retrieved(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case RETRIEVE_MAIN:
      monitor->state[MAIN] = EXPLORE_MAIN;
      break;
    default:
      raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "retrieved", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "retrieved", "DEFAULT");
      break;
  }
}

void raise_retrieved(_Explorer* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, RETRIEVED, p_head);
}

void call_next_action(_Explorer *monitor) {
  switch (monitor->action_queue->id) {
    case DRIVE: ;
      int x_drive = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      int y_drive = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      int heading_drive = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      drive(monitor, x_drive, y_drive, heading_drive);
      break;
    case TURN: ;
      int facing_turn = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      turn(monitor, facing_turn);
      break;
    case SCAN_VIEW: ;
      int x_view = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      int y_view = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      int heading_view = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      const void *map_view = monitor->action_queue->params->v;
      pop_param(&monitor->action_queue->params);
      scan_view(monitor, x_view, y_view, heading_view, map_view);
      break;
    case FOUND: ;
      found(monitor);
      break;
    case RETRIEVED: ;
      retrieved(monitor);
      break;
  }
}

void exec_actions(_Explorer *monitor) {
  while(monitor->action_queue != NULL) {
    call_next_action(monitor);
    pop_action(&monitor->action_queue);
  }
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

