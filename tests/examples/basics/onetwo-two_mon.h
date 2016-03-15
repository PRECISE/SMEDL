#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define ONETWOTWO_MONITOR_MAP_SIZE 100 // number of buckets
#define ONETWOTWO_MONITOR_IDENTITIES 1

typedef struct OnetwotwoData {
  void* id;

} OnetwotwoData;

typedef struct OnetwotwoMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];

  action *action_queue;
} OnetwotwoMonitor;

typedef struct OnetwotwoMonitorRecord {
  OnetwotwoMonitor *monitor;
  struct OnetwotwoMonitorRecord *next;
} OnetwotwoMonitorRecord;

typedef struct OnetwotwoMonitorMap {
  OnetwotwoMonitorRecord *list[ONETWOTWO_MONITOR_MAP_SIZE];
} OnetwotwoMonitorMap;

OnetwotwoMonitorMap* onetwotwo_monitor_maps[ONETWOTWO_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t onetwotwo_monitor_maps_lock;

OnetwotwoMonitor* init_onetwotwo_monitor(OnetwotwoData*);

/*
 * Monitor Event Handlers
 */
void onetwotwo_foo(OnetwotwoMonitor* monitor);
void raise_onetwotwo_foo(OnetwotwoMonitor* monitor);
void onetwotwo_bar(OnetwotwoMonitor* monitor);
void raise_onetwotwo_bar(OnetwotwoMonitor* monitor);

/*
 * Monitor Utility Functions
 */
OnetwotwoMonitorRecord* get_onetwotwo_monitors();
OnetwotwoMonitorRecord* get_onetwotwo_monitors_by_identity(int, int, void*);
OnetwotwoMonitorRecord* filter_onetwotwo_monitors_by_identity(OnetwotwoMonitorRecord*, int, void*);
int init_onetwotwo_monitor_maps();
int add_onetwotwo_monitor_to_map(OnetwotwoMonitor*, int);
int put_onetwotwo_monitor(OnetwotwoMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_onetwotwo_monitor();
void free_onetwotwo_monitor_maps();