#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define MINIMAL_MONITOR_MAP_SIZE 100 // number of buckets
#define MINIMAL_MONITOR_IDENTITIES 1

typedef struct MinimalData {
  void* id;

} MinimalData;

typedef struct MinimalMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];

  action *action_queue;
} MinimalMonitor;

typedef struct MinimalMonitorRecord {
  MinimalMonitor *monitor;
  struct MinimalMonitorRecord *next;
} MinimalMonitorRecord;

typedef struct MinimalMonitorMap {
  MinimalMonitorRecord *list[MINIMAL_MONITOR_MAP_SIZE];
} MinimalMonitorMap;

MinimalMonitorMap* minimal_monitor_maps[MINIMAL_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t minimal_monitor_maps_lock;

MinimalMonitor* init_minimal_monitor(MinimalData*);

/*
 * Monitor Event Handlers
 */
void minimal_foo(MinimalMonitor* monitor);
void raise_minimal_foo(MinimalMonitor* monitor);

/*
 * Monitor Utility Functions
 */
MinimalMonitorRecord* get_minimal_monitors();
MinimalMonitorRecord* get_minimal_monitors_by_identity(int, int, void*);
MinimalMonitorRecord* filter_minimal_monitors_by_identity(MinimalMonitorRecord*, int, void*);
int init_minimal_monitor_maps();
int add_minimal_monitor_to_map(MinimalMonitor*, int);
int put_minimal_monitor(MinimalMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_minimal_monitor();
void free_minimal_monitor_maps();