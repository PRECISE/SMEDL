#ifndef ACTIONS_H
#define ACTIONS_H

#include "mon_utils.h"
#include "cJSON.h"

typedef struct Parameter param;
struct Parameter {
    int type;
    int i;
    char c;
    double d;
    const void *v;
    cJSON *provenance;
    param *next;
};

int push_param(param**, int*, char*, double*, const void**, cJSON *);
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
