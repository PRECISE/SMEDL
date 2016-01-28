#include <stdlib.h>
#include <stdio.h>
#include "actions.h"

typedef enum { SC1, SC2 } scenario;
typedef enum { SAFEMON_SC1, SWITCH_SC1 } sc1_state;
typedef enum { ONE_SC2, TWO_SC2 } sc2_state;
typedef enum { UPDATEPOS, CHANGEDIR, CLICK } event;
typedef enum { DEFAULT } error_type;
const char *sc1_states[2] = {"SafeMon", "Switch"};
const char *sc2_states[2] = {"One", "Two"};

typedef struct _SafeMon{
  int upbound;
  int lobound;
  int state[2]; // = { SAFEMON_SC1, ONE_SC2 };
  const char **state_names[2];
  action *action_queue;
} _SafeMon;

void call_next_action(_SafeMon*);
void raise_error(char*, const char*, char*, char*);

_SafeMon* init_SafeMon() {
  _SafeMon* monitor = (_SafeMon*)malloc(sizeof(_SafeMon));
  monitor->state[0] = SAFEMON_SC1;
  monitor->state[1] = ONE_SC2;
  monitor->state_names[0] = sc1_states;
  monitor->state_names[1] = sc2_states;
  return monitor;
}

void updatePos(_SafeMon* monitor, int pos, char c) {
  switch (monitor->state[SC1]) {
    case SAFEMON_SC1:
      if(pos == monitor->upbound || pos == monitor->lobound) {
        monitor->state[SC1] = SWITCH_SC1;
      } else {
        monitor->state[SC1] = SAFEMON_SC1;
      }
      break;
    default:
      raise_error("sc1", monitor->state_names[SC1][monitor->state[SC1]], "updatePos", "DEFAULT");
      break;
  }
  switch (monitor->state[SC2]) {
    case ONE_SC2:
      monitor->state[SC2] = ONE_SC2;
      break;
    case TWO_SC2:
      monitor->state[SC2] = TWO_SC2;
      break;
    default:
      raise_error("sc2", monitor->state_names[SC2][monitor->state[SC2]], "updatePos", "DEFAULT");
      break;
  }
}

void raise_updatePos(_SafeMon* monitor, int pos, char c) {
  param *p_head = NULL;
  push_param(&p_head, &pos, NULL, NULL);
  push_param(&p_head, NULL, &c, NULL);
  push_action(&monitor->action_queue, UPDATEPOS, p_head);
}

void changeDir(_SafeMon* monitor) {
  switch (monitor->state[SC1]) {
    case SWITCH_SC1:
      monitor->state[SC1] = SAFEMON_SC1;
      break;
    case SAFEMON_SC1:
      monitor->state[SC1] = SAFEMON_SC1;
      break;
    default:
      raise_error("sc1", monitor->state_names[SC1][monitor->state[SC1]], "changeDir", "DEFAULT");
      break;
  }
  switch (monitor->state[SC2]) {
    case ONE_SC2:
      monitor->state[SC2] = ONE_SC2;
      break;
    case TWO_SC2:
      monitor->state[SC2] = TWO_SC2;
      break;
    default:
      raise_error("sc2", monitor->state_names[SC2][monitor->state[SC2]], "changeDir", "DEFAULT");
      break;
  }
}

void raise_changeDir(_SafeMon* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, CHANGEDIR, p_head);
}

void click(_SafeMon* monitor) {
  switch (monitor->state[SC1]) {
    case SAFEMON_SC1:
      monitor->state[SC1] = SAFEMON_SC1;
      break;
    case SWITCH_SC1:
      monitor->state[SC1] = SWITCH_SC1;
      break;
    default:
      raise_error("sc1", monitor->state_names[SC1][monitor->state[SC1]], "click", "DEFAULT");
      break;
  }
  switch (monitor->state[SC2]) {
    case ONE_SC2:
      monitor->state[SC2] = TWO_SC2;
      break;
    case TWO_SC2:
      monitor->state[SC2] = ONE_SC2;
      break;
    default:
      raise_error("sc2", monitor->state_names[SC2][monitor->state[SC2]], "click", "DEFAULT");
      break;
  }
}

void raise_click(_SafeMon* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, CLICK, p_head);
}

void set_safemon_upbound(_SafeMon *monitor, int new_upbound) {
  monitor->upbound = new_upbound;
  return;
}

void set_safemon_lobound(_SafeMon *monitor, int new_lobound) {
  monitor->lobound = new_lobound;
  return;
}

void call_next_action(_SafeMon *monitor) {
  switch (monitor->action_queue->id) {
    case UPDATEPOS: ;
      int pos_updatePos = monitor->action_queue->params->i;
      pop_param(&monitor->action_queue->params);
      char c_updatePos = monitor->action_queue->params->c;
      pop_param(&monitor->action_queue->params);
      updatePos(monitor, pos_updatePos, c_updatePos);
      break;
    case CHANGEDIR: ;
      changeDir(monitor);
      break;
    case CLICK: ;
      click(monitor);
      break;
  }
}

void exec_actions(_SafeMon *monitor) {
  while(monitor->action_queue != NULL) {
    call_next_action(monitor);
    pop_action(&monitor->action_queue);
  }
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

