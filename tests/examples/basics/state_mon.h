#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define STATE_MONITOR_MAP_SIZE 100 // number of buckets
#define STATE_MONITOR_IDENTITIES 1

typedef struct StateData {
  void* id;
  int bar;
} StateData;

typedef struct StateMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int bar;
  action *action_queue;
} StateMonitor;

typedef struct StateMonitorRecord {
  StateMonitor *monitor;
  struct StateMonitorRecord *next;
} StateMonitorRecord;

typedef struct StateMonitorMap {
  StateMonitorRecord *list[STATE_MONITOR_MAP_SIZE];
} StateMonitorMap;

StateMonitorMap* state_monitor_maps[STATE_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t state_monitor_maps_lock;

StateMonitor* init_state_monitor(StateData*);

/*
 * Monitor Event Handlers
 */
void state_foo(StateMonitor* monitor, int x);
void raise_state_foo(StateMonitor* monitor, int x);

/*
 * Monitor Utility Functions
 */
StateMonitorRecord* get_state_monitors();
StateMonitorRecord* get_state_monitors_by_identity(int, int, void*);
StateMonitorRecord* filter_state_monitors_by_identity(StateMonitorRecord*, int, void*);
int init_state_monitor_maps();
int add_state_monitor_to_map(StateMonitor*, int);
int put_state_monitor(StateMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_state_monitor();
void free_state_monitor_maps();