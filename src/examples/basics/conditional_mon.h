#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define CONDITIONAL_MONITOR_MAP_SIZE 100 // number of buckets
#define CONDITIONAL_MONITOR_IDENTITIES 1

typedef struct ConditionalData {
  void* id;
  int bar;
} ConditionalData;

typedef struct ConditionalMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int bar;
  action *action_queue;
} ConditionalMonitor;

typedef struct ConditionalMonitorRecord {
  ConditionalMonitor *monitor;
  struct ConditionalMonitorRecord *next;
} ConditionalMonitorRecord;

typedef struct ConditionalMonitorMap {
  ConditionalMonitorRecord *list[CONDITIONAL_MONITOR_MAP_SIZE];
} ConditionalMonitorMap;

ConditionalMonitorMap* conditional_monitor_maps[CONDITIONAL_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t conditional_monitor_maps_lock;

ConditionalMonitor* init_conditional_monitor(ConditionalData*);

/*
 * Monitor Event Handlers
 */
void conditional_foo(ConditionalMonitor* monitor, int x);
void raise_conditional_foo(ConditionalMonitor* monitor, int x);

/*
 * Monitor Utility Functions
 */
ConditionalMonitorRecord* get_conditional_monitors();
ConditionalMonitorRecord* get_conditional_monitors_by_identity(int, int, void*);
ConditionalMonitorRecord* filter_conditional_monitors_by_identity(ConditionalMonitorRecord*, int, void*);
int init_conditional_monitor_maps();
int add_conditional_monitor_to_map(ConditionalMonitor*, int);
int put_conditional_monitor(ConditionalMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_conditional_monitor();
void free_conditional_monitor_maps();