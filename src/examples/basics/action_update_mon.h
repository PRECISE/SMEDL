#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define ACTUP_MONITOR_MAP_SIZE 100 // number of buckets
#define ACTUP_MONITOR_IDENTITIES 0

typedef struct ActupData {  

  int bar;
} ActupData;

typedef struct ActupMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[0];
  int state[1];
  int bar;
  action *action_queue;
} ActupMonitor;

typedef struct ActupMonitorRecord {
  ActupMonitor *monitor;
  struct ActupMonitorRecord *next;
} ActupMonitorRecord;

typedef struct ActupMonitorMap {
  ActupMonitorRecord *list[ACTUP_MONITOR_MAP_SIZE];
} ActupMonitorMap;

ActupMonitorMap* actup_monitor_maps[ACTUP_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t actup_monitor_maps_lock;

ActupMonitor* init_actup_monitor(ActupData*);
int init_actup_monitor_maps();
int add_actup_monitor_to_map(ActupMonitor*, int);
int put_actup_monitor(ActupMonitor*); //puts into all maps
ActupMonitorRecord* get_actup_monitors();
ActupMonitorRecord* get_actup_monitors_by_identity(int, int, void*);
ActupMonitorRecord* filter_actup_monitors_by_identity(ActupMonitorRecord*, int, void*);
void actup_foo(ActupMonitor* monitor, int x);
void raise_actup_foo(ActupMonitor* monitor, int x);
void raise_error(char*, const char*, char*, char*);
void free_actup_monitor();
void free_actup_monitor_maps();