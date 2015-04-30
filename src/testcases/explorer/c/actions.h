#ifndef ACTIONS_H
#define ACTIONS_H

typedef struct Parameter param;
struct Parameter {
  int type;
  int i;
  char c;
  double d;
  param *next;
};

int push_param(param**, int*, char*, double*);
void pop_param(param**);

typedef struct Action action;
struct Action {
  int id;
  param *params;
  action *next;
};

int push_action(action**, int, param*);
void pop_action(action**);

#endif