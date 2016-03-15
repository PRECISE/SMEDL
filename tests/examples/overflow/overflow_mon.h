#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define OVFMON_MONITOR_MAP_SIZE 100 // number of buckets
#define OVFMON_MONITOR_IDENTITIES 1

typedef struct OvfmonData {
  void* buffer;
  int size;
} OvfmonData;

typedef struct OvfmonMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int size;
  action *action_queue;
} OvfmonMonitor;

typedef struct OvfmonMonitorRecord {
  OvfmonMonitor *monitor;
  struct OvfmonMonitorRecord *next;
} OvfmonMonitorRecord;

typedef struct OvfmonMonitorMap {
  OvfmonMonitorRecord *list[OVFMON_MONITOR_MAP_SIZE];
} OvfmonMonitorMap;

OvfmonMonitorMap* ovfmon_monitor_maps[OVFMON_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t ovfmon_monitor_maps_lock;

OvfmonMonitor* init_ovfmon_monitor(OvfmonData*);

/*
 * Monitor Event Handlers
 */
void ovfmon_reinit(OvfmonMonitor* monitor, int new_siz);
void raise_ovfmon_reinit(OvfmonMonitor* monitor, int new_siz);
void ovfmon_write(OvfmonMonitor* monitor, int wsiz);
void raise_ovfmon_write(OvfmonMonitor* monitor, int wsiz);

/*
 * Monitor Utility Functions
 */
OvfmonMonitorRecord* get_ovfmon_monitors();
OvfmonMonitorRecord* get_ovfmon_monitors_by_identity(int, int, void*);
OvfmonMonitorRecord* filter_ovfmon_monitors_by_identity(OvfmonMonitorRecord*, int, void*);
int init_ovfmon_monitor_maps();
int add_ovfmon_monitor_to_map(OvfmonMonitor*, int);
int put_ovfmon_monitor(OvfmonMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_ovfmon_monitor();
void free_ovfmon_monitor_maps();