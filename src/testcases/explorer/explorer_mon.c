#include <stdlib.h>
#include <stdio.h>
#include "helper.h"

typedef enum { MAIN, EXPLORE, RETRIEVE } scenario;
typedef enum { EXPLORE_MAIN, RETRIEVE_MAIN } main_state;
typedef enum { EXPLORE_EXPLORE, RETRIEVE_EXPLORE, SCAN_EXPLORE, GEN0_EXPLORE } explore_state;
typedef enum { RETRIEVE_RETRIEVE, EXPLORE_RETRIEVE } retrieve_state;
typedef enum { DEFAULT } error_type;
const char *main_states[2] = {"Explore", "Retrieve"};
const char *explore_states[4] = {"Explore", "Retrieve", "Scan", "Gen0"};
const char *retrieve_states[2] = {"Retrieve", "Explore"};

typedef struct _Explorer{
  int interest_threshold;
  int y;
  int x;
  int heading;
  int state[3]; // = { EXPLORE_MAIN, EXPLORE_EXPLORE, RETRIEVE_RETRIEVE };
  const char **state_names[3];
} _Explorer;

void raise_error(char*, const char*, char*, char*);

_Explorer* init_Explorer() {
  _Explorer* monitor = (_Explorer*)malloc(sizeof(_Explorer));
  monitor->state[0] = EXPLORE_MAIN;
  monitor->state[1] = EXPLORE_EXPLORE;
  monitor->state[2] = RETRIEVE_RETRIEVE;
  monitor->state_names[0] = main_states;
  monitor->state_names[1] = explore_states;
  monitor->state_names[2] = retrieve_states;
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
  switch (monitor->state[RETRIEVE]) {
    case RETRIEVE_RETRIEVE:
      monitor->state[RETRIEVE] = EXPLORE_RETRIEVE;
      break;
    default:
      raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "retrieved", "DEFAULT");
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
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    case RETRIEVE_RETRIEVE:
      if(x != monitor->x && y != monitor->y) {
        monitor->state[RETRIEVE] = RETRIEVE_RETRIEVE;
      } else {
        raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "drive", "DEFAULT");
      }
      break;
    default:
      raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "drive", "DEFAULT");
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
    case SCAN_EXPLORE:
      if(facing != monitor->heading) {
        monitor->state[EXPLORE] = GEN0_EXPLORE;
      } else {
        raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    default:
      raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "turn", "DEFAULT");
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
  switch (monitor->state[RETRIEVE]) {
    default:
      raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "found", "DEFAULT");
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
    case EXPLORE_EXPLORE:
      if(contains_object(x, y)) {
        monitor->state[EXPLORE] = RETRIEVE_EXPLORE;
      } else {
        raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      }
      break;
    default:
      raise_error("explore", monitor->state_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
      break;
  }
  switch (monitor->state[RETRIEVE]) {
    default:
      raise_error("retrieve", monitor->state_names[RETRIEVE][monitor->state[RETRIEVE]], "view", "DEFAULT");
      break;
  }
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

