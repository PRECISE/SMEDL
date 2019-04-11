#ifndef {{ base_file_name|upper }}_MON_H
#define {{ base_file_name|upper }}_MON_H

#define {{ obj|upper }}_MONITOR_IDENTITIES {{ identities|length }}

#include "monitor_map.h"
#include "actions.h"
{%- if multithreaded %}{{ '\n' }}#include <pthread.h>{% endif %}


typedef enum { {{ identities_names|join(', ') }} } {{ obj|lower }}_identity;
typedef enum { {{ scenario_names|join(', ') }} } {{ obj|lower }}_scenario;
{{ state_enums }}
typedef enum { {{ event_enums }} } {{ obj|lower }}_event;
typedef enum { {{ error_enums }} } {{ obj|lower }}_error;

typedef struct {{ obj|title }}Data {
{{ identity_declarations }}
{{ state_var_declarations }}
} {{ obj|title }}Data;

typedef struct {{ obj|title }}Monitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[{{ identities|length }}];
  int state[{{ scenario_names|length }}];
{{ state_var_declarations }}
  action *action_queue;
    int recycleFlag;
} {{ obj|title }}Monitor;

typedef struct {{ obj|title }}MonitorPoolRecord {
  {{ obj|title }}Monitor *monitor;
  struct {{ obj|title }}MonitorPoolRecord *next;
} {{ obj|title }}MonitorPoolRecord;


{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor({{ obj|title }}Data*);
{{ obj|title }}Monitor* init_default_{{ obj|lower }}_monitor();
void free_{{ obj|lower}}_monitor({{ obj|title }}Monitor*);

/*
 * Monitor Event Handlers
 */
{{ signatures|join(';\n') }};

/*
 * Monitor Utility Functions
 */

{{ obj|title }}Monitor* {{ obj|lower }}_getMonitorObject();
int {{ obj|lower }}_addMonitorObjectToPool({{ obj|title }}MonitorPoolRecord*);

char* monitor_identities_str_{{ obj|lower }}(MonitorIdentity**);
void executePendingEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor);
void executeEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor);

#endif //{{ base_file_name|upper }}_MON_H
