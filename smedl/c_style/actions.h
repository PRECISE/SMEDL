#ifndef ACTIONS_H
#define ACTIONS_H

#include "monitor_map.h"
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

#ifdef DEBUG
void print_param(param*, char*);
#endif //DEBUG

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

typedef struct GlobalAction global_action;
struct GlobalAction {
    // Identifies the monitor type. See the set1_Monitor_Type enum in set1_global_wrapper.c/.h
    int monitor_type;
    // It seems monitors can have more than one ID variable, but we need to be flexible,
    // so we will just use a double pointer instead of a pointer to array.
    MonitorIdentity **identities;
    int id; //This identifies the event type within this monitor type. See windowmanager_event
            // enum in windowManager_mon.c for an example.
    param *params;
    global_action *next;
};

int push_global_action(global_action**, int, MonitorIdentity**, int, param*);
void pop_global_action(global_action**);

#endif
