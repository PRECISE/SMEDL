#include <stdlib.h>
#include <stdio.h>
#include "helper.h"

typedef enum { MAIN, EXPLORE } scenario;
typedef enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_state;
typedef enum { LOOK_EXPLORE, MOVE_EXPLORE } explore_state;
typedef enum { DEFAULT } error_type;
const char *main_states[2] = {"Explore", "Retrieve"};
const char *explore_states[2] = {"Look", "Move"};

typedef struct _Explorer{
  int interest_threshold;
  int y;
  int x;
  int heading;
  int state[2]; // = { EXPLORE_MAIN, LOOK_EXPLORE };
  const char **state_names[2];
} _Explorer;

void raise_error(char*, const char*, char*, char*);

_Explorer* init_Explorer() {
  _Explorer* monitor = (_Explorer*)malloc(sizeof(_Explorer));
  monitor->state[0] = EXPLORE_MAIN;
  monitor->state[1] = LOOK_EXPLORE;
  monitor->state_names[0] = main_states;
  monitor->state_names[1] = explore_states;
  return monitor;
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
        raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
      break;
  }
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
        raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
      break;
  }
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
        raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      break;
  }
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

