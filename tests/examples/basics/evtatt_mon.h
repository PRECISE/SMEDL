#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define EVTATT_MONITOR_MAP_SIZE 100 // number of buckets
#define EVTATT_MONITOR_IDENTITIES 1

typedef struct EvtattData {
  void* id;

} EvtattData;

typedef struct EvtattMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];

  action *action_queue;
} EvtattMonitor;

typedef struct EvtattMonitorRecord {
  EvtattMonitor *monitor;
  struct EvtattMonitorRecord *next;
} EvtattMonitorRecord;

typedef struct EvtattMonitorMap {
  EvtattMonitorRecord *list[EVTATT_MONITOR_MAP_SIZE];
} EvtattMonitorMap;

EvtattMonitorMap* evtatt_monitor_maps[EVTATT_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t evtatt_monitor_maps_lock;

EvtattMonitor* init_evtatt_monitor(EvtattData*);

/*
 * Monitor Event Handlers
 */
void evtatt_foo(EvtattMonitor* monitor, int x);
void raise_evtatt_foo(EvtattMonitor* monitor, int x);

/*
 * Monitor Utility Functions
 */
EvtattMonitorRecord* get_evtatt_monitors();
EvtattMonitorRecord* get_evtatt_monitors_by_identity(int, int, void*);
EvtattMonitorRecord* filter_evtatt_monitors_by_identity(EvtattMonitorRecord*, int, void*);
int init_evtatt_monitor_maps();
int add_evtatt_monitor_to_map(EvtattMonitor*, int);
int put_evtatt_monitor(EvtattMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_evtatt_monitor();
void free_evtatt_monitor_maps();