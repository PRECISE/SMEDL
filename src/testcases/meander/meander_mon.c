#include <stdlib.h>
#include <stdio.h>

typedef enum { SC1 } scenario;
typedef enum { SAFEMON_SC1, SWITCH_SC1 } sc1_state;
typedef enum { DEFAULT } error_type;
const char *sc1_states[2] = {"SafeMon", "Switch"};

typedef struct _SafeMon{
  int upbound;
  int lobound;
  int state[1]; // = { SAFEMON_SC1 };
  const char **state_names[1];
} _SafeMon;

void raise_error(char*, const char*, char*, char*);

_SafeMon* init_SafeMon() {
  _SafeMon* monitor = (_SafeMon*)malloc(sizeof(_SafeMon));
  monitor->state[0] = SAFEMON_SC1;
  monitor->state_names[0] = sc1_states;
  return monitor;
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
}

void updatePos(_SafeMon* monitor, int pos) {
  switch (monitor->state[SC1]) {
    case SAFEMON_SC1:
      if(pos == monitor->upbound || pos == monitor->lobound) {
        monitor->state[SC1] = SWITCH_SC1;
      } else {
        raise_error("sc1", monitor->state_names[SC1][monitor->state[SC1]], "updatePos", "DEFAULT");
      }
      break;
    default:
      raise_error("sc1", monitor->state_names[SC1][monitor->state[SC1]], "updatePos", "DEFAULT");
      break;
  }
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

