#include <stdlib.h>
#include <stdio.h>
#include "actions.h"
#include "explorer_mon.h"


typedef enum { MAIN, EXPLORE } scenario;
typedef enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_state;
typedef enum { MOVE_EXPLORE, LOOK_EXPLORE } explore_state;
typedef enum { DRIVE, TURN, VIEW, FOUND, RETRIEVED } event;
typedef enum { DEFAULT } error_type;
const char *main_states[2] = {"Explore", "Retrieve"};
const char *explore_states[2] = {"Move", "Look"};

typedef struct _Explorer{
  int interest_threshold;
  int y;
  int x;
  int heading;
  int state[2]; // = { EXPLORE_MAIN, MOVE_EXPLORE };
  const char **state_names[2];
  action *action_queue;
} _Explorer;

void call_next_action(_Explorer*);
void raise_error(char*, const char*, char*, char*);

_Explorer* init_Explorer(int interest_threshold, int y, int x, int heading) {
  _Explorer* monitor = (_Explorer*)malloc(sizeof(_Explorer));
  monitor->state[0] = EXPLORE_MAIN;
  monitor->state[1] = MOVE_EXPLORE;
  monitor->state_names[0] = main_states;
  monitor->state_names[1] = explore_states;
  return monitor;
}

void drive(_Explorer* monitor, int x, int y, int heading) {
  switch (monitor->state[MAIN]) {
    default:
      raise_error("main", monitor->state_names[MAIN][monitor->state[MAIN]], "drive", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case MOVE_EXPLORE:
      if(x == monitor->x && y == monitor->y) {
        monitor->state[EXPLORE] = LOOK_EXPLORE;
      } else {
        monitor->state[EXPLORE] = LOOK_EXPLORE;
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
      break;
  }
}

void raise_drive(_Explorer* monitor, int x, int y, int heading) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_param(&p_head, &heading, NULL, NULL, NULL);
  push_action(&monitor->action_queue, DRIVE, p_head);
}

void turn(_Explorer* monitor, int facing) {
  switch (monitor->state[MAIN]) {
    default:
      raise_error("main", monitor->state_names[MAIN][monitor->state[MAIN]], "turn", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case MOVE_EXPLORE:
      if(facing != monitor->heading) {
        monitor->state[EXPLORE] = LOOK_EXPLORE;
      } else {
        monitor->state[EXPLORE] = MOVE_EXPLORE;
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
      break;
  }
}

void raise_turn(_Explorer* monitor, int facing) {
  param *p_head = NULL;
  push_param(&p_head, &facing, NULL, NULL, NULL);
  push_action(&monitor->action_queue, TURN, p_head);
}

void view(_Explorer* monitor, int x, int y) {
  switch (monitor->state[MAIN]) {
    default:
      raise_error("main", monitor->state_names[MAIN][monitor->state[MAIN]], "view", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    case LOOK_EXPLORE:
      if(contains_object(x, y)) {
        monitor->state[EXPLORE] = MOVE_EXPLORE;
      } else {
        monitor->state[EXPLORE] = MOVE_EXPLORE;
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      break;
  }
}

void raise_view(_Explorer* monitor, int x, int y) {
  param *p_head = NULL;
  push_param(&p_head, &x, NULL, NULL, NULL);
  push_param(&p_head, &y, NULL, NULL, NULL);
  push_action(&monitor->action_queue, VIEW, p_head);
}

void found(_Explorer* monitor) {
  switch (monitor->state[MAIN]) {
    case EXPLORE_MAIN:
      monitor->state[MAIN] = RETRIEVE_MAIN;
      break;
    default:
      raise_error("main", monitor->state_names[MAIN][monitor->state[MAIN]], "found", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "found", "DEFAULT");
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
      raise_error("main", monitor->state_names[MAIN][monitor->state[MAIN]], "retrieved", "DEFAULT");
      break;
  }
  switch (monitor->state[EXPLORE]) {
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "retrieved", "DEFAULT");
      break;
  }
}

void raise_retrieved(_Explorer* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, RETRIEVED, p_head);
}

void set_explorer_interest_threshold(_Explorer *monitor, int new_interest_threshold) {
  monitor->interest_threshold = new_interest_threshold;
  return;
}

void set_explorer_y(_Explorer *monitor, int new_y) {
  monitor->y = new_y;
  return;
}

void set_explorer_x(_Explorer *monitor, int new_x) {
  monitor->x = new_x;
  return;
}

void set_explorer_heading(_Explorer *monitor, int new_heading) {
  monitor->heading = new_heading;
  return;
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
    case VIEW: ;
      int x_view = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      int y_view = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      view(monitor, x_view, y_view);
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

// Checker Storage Functions

typedef struct CheckerRecord {
  _Explorer* checker;
  struct CheckerRecord* next;
} CheckerRecord;

CheckerRecord* checkStore;

void initCheckerStorage() {
  checkStore = NULL;
}

void addChecker( _Explorer* c) {
  CheckerRecord* tmp = checkStore;
  checkStore = (CheckerRecord*)malloc(sizeof(CheckerRecord));
  checkStore->checker = c;
  checkStore->next = tmp;
}

_Explorer* getChecker( _Explorer* key ) {
  CheckerRecord* iter = checkStore;
  while (iter != NULL) {
    if (iter->checker == key)
       break;
    iter = iter->next;
  }
  return iter->checker;
}

