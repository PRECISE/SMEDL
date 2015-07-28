#include "monitor_map.h"

#define {{obj|upper}}_MONITOR_MAP_SIZE 100 // number of buckets
#define {{obj|upper}}_MONITOR_IDENTITIES {{num_identities}}

typedef struct {{obj|title}}Data {  
{{identity_declarations}}
{{state_var_declarations}}
} {{obj|title}}Data;

typedef struct {{obj|title}}Monitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[{{num_identities}}];
{{state_var_declarations}}
} {{obj|title}}Monitor;

typedef struct {{obj|title}}MonitorRecord {
  {{obj|title}}Monitor *monitor;
  struct {{obj|title}}MonitorRecord *next;
} {{obj|title}}MonitorRecord;

typedef struct {{obj|title}}MonitorMap {
  {{obj|title}}MonitorRecord *list[{{obj|upper}}_MONITOR_MAP_SIZE];
} {{obj|title}}MonitorMap;

{{obj|title}}MonitorMap* {{obj|lower}}_monitor_maps[{{obj|upper}}_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t {{obj|lower}}_monitor_maps_lock;

{{obj|title}}Monitor* init_{{obj|lower}}_monitor({{obj|title}}Data*);
int init_{{obj|lower}}_monitor_maps();
int add_{{obj|lower}}_monitor_to_map({{obj|title}}Monitor*, int);
int put_{{obj|lower}}_monitor({{obj|title}}Monitor*); //puts into all maps
{{obj|title}}MonitorRecord* get_{{obj|lower}}_monitors();
{{obj|title}}MonitorRecord* get_{{obj|lower}}_monitors_by_identity(int, int, void*);
{{obj|title}}MonitorRecord* filter_{{obj|lower}}_monitors_by_identity({{obj|title}}MonitorRecord*, int, void*);
void free_{{obj|lower}}_monitor();
void free_{{obj|lower}}_monitor_maps();
