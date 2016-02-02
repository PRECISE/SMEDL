#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define ELSENOACTION_MONITOR_MAP_SIZE 100 // number of buckets
#define ELSENOACTION_MONITOR_IDENTITIES 1

typedef struct ElsenoactionData {
  void* id;
  int bar;
} ElsenoactionData;

typedef struct ElsenoactionMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int bar;
  action *action_queue;
} ElsenoactionMonitor;

typedef struct ElsenoactionMonitorRecord {
  ElsenoactionMonitor *monitor;
  struct ElsenoactionMonitorRecord *next;
} ElsenoactionMonitorRecord;

typedef struct ElsenoactionMonitorMap {
  ElsenoactionMonitorRecord *list[ELSENOACTION_MONITOR_MAP_SIZE];
} ElsenoactionMonitorMap;

ElsenoactionMonitorMap* elsenoaction_monitor_maps[ELSENOACTION_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t elsenoaction_monitor_maps_lock;

ElsenoactionMonitor* init_elsenoaction_monitor(ElsenoactionData*);

/*
 * Monitor Event Handlers
 */
void elsenoaction_foo(ElsenoactionMonitor* monitor, int x);
void raise_elsenoaction_foo(ElsenoactionMonitor* monitor, int x);

/*
 * Monitor Utility Functions
 */
ElsenoactionMonitorRecord* get_elsenoaction_monitors();
ElsenoactionMonitorRecord* get_elsenoaction_monitors_by_identity(int, int, void*);
ElsenoactionMonitorRecord* filter_elsenoaction_monitors_by_identity(ElsenoactionMonitorRecord*, int, void*);
int init_elsenoaction_monitor_maps();
int add_elsenoaction_monitor_to_map(ElsenoactionMonitor*, int);
int put_elsenoaction_monitor(ElsenoactionMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_elsenoaction_monitor();
void free_elsenoaction_monitor_maps();