#ifndef {{ base_file_name|upper }}_MON_H
#define {{ base_file_name|upper }}_MON_H

#include "monitor_map.h"
#include "actions.h"
{%- if multithreaded %}{{ '\n' }}#include <pthread.h>{% endif %}

#define {{ obj|upper }}_MONITOR_MAP_SIZE 100 // number of buckets
#define {{ obj|upper }}_MONITOR_IDENTITIES {{ identities|length }}

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

typedef struct {{ obj|title }}MonitorRecord {
  {{ obj|title }}Monitor *monitor;
  struct {{ obj|title }}MonitorRecord *next;
} {{ obj|title }}MonitorRecord;

typedef struct {{ obj|title }}MonitorMap {
  {{ obj|title }}MonitorRecord *list[{{ obj|upper }}_MONITOR_MAP_SIZE];
} {{ obj|title }}MonitorMap;

{{ obj|title }}MonitorMap* {{ obj|lower }}_monitor_maps[{{ obj|upper }}_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t {{ obj|lower }}_monitor_maps_lock;

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor({{ obj|title }}Data*);
void free_{{ obj|lower}}_monitor({{ obj|title }}Monitor*);

/*
 * Monitor Event Handlers
 */
{{ signatures|join(';\n') }};

/*
 * Monitor Utility Functions
 */

{{ obj|title }}Monitor* {{ obj|lower }}_getMonitorObject();
int {{ obj|lower }}_addMonitorObjectToPool({{ obj|title }}MonitorRecord*);
int remove_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity);
void remove_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) ;


{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors();
{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors_by_identity(int, int, void*);
{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identities(int[], int type, void *[],int);
{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord*, int, void*);
int init_{{ obj|lower }}_monitor_maps();
void free_{{ obj|lower }}_monitor_maps();
int add_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor*, int);
int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor*); //puts into all maps
char* monitor_identities_str_{{ obj|lower }}(MonitorIdentity**);
void executePendingEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor);
void executeEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor);

#endif //{{ base_file_name|upper }}_MON_H
