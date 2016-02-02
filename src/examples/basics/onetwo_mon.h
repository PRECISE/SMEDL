#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define ONETWOMON_MONITOR_MAP_SIZE 100 // number of buckets
#define ONETWOMON_MONITOR_IDENTITIES 1

typedef struct OnetwomonData {
  void* id;

} OnetwomonData;

typedef struct OnetwomonMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];

  action *action_queue;
} OnetwomonMonitor;

typedef struct OnetwomonMonitorRecord {
  OnetwomonMonitor *monitor;
  struct OnetwomonMonitorRecord *next;
} OnetwomonMonitorRecord;

typedef struct OnetwomonMonitorMap {
  OnetwomonMonitorRecord *list[ONETWOMON_MONITOR_MAP_SIZE];
} OnetwomonMonitorMap;

OnetwomonMonitorMap* onetwomon_monitor_maps[ONETWOMON_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t onetwomon_monitor_maps_lock;

OnetwomonMonitor* init_onetwomon_monitor(OnetwomonData*);

/*
 * Monitor Event Handlers
 */
void onetwomon_foo(OnetwomonMonitor* monitor);
void raise_onetwomon_foo(OnetwomonMonitor* monitor);

/*
 * Monitor Utility Functions
 */
OnetwomonMonitorRecord* get_onetwomon_monitors();
OnetwomonMonitorRecord* get_onetwomon_monitors_by_identity(int, int, void*);
OnetwomonMonitorRecord* filter_onetwomon_monitors_by_identity(OnetwomonMonitorRecord*, int, void*);
int init_onetwomon_monitor_maps();
int add_onetwomon_monitor_to_map(OnetwomonMonitor*, int);
int put_onetwomon_monitor(OnetwomonMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_onetwomon_monitor();
void free_onetwomon_monitor_maps();