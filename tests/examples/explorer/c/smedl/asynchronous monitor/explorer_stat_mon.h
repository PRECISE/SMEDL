#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <pthread.h>
#include "czmq.h"

#define EXPLORER_STAT_MONITOR_MAP_SIZE 100 // number of buckets
#define EXPLORER_STAT_MONITOR_IDENTITIES 1

typedef struct Explorer_statData {
  void* id;
  int sum;
  int sum_count;
  int targetNum;
} Explorer_statData;

typedef struct Explorer_statMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int sum;
  int sum_count;
  int targetNum;
  action *action_queue;
  FILE *logFile;
  zsock_t *publisher;
  zsock_t *subscriber;
} Explorer_statMonitor;

typedef struct Explorer_statMonitorRecord {
  Explorer_statMonitor *monitor;
  struct Explorer_statMonitorRecord *next;
} Explorer_statMonitorRecord;

typedef struct Explorer_statMonitorMap {
  Explorer_statMonitorRecord *list[EXPLORER_STAT_MONITOR_MAP_SIZE];
} Explorer_statMonitorMap;

Explorer_statMonitorMap* explorer_stat_monitor_maps[EXPLORER_STAT_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t explorer_stat_monitor_maps_lock;

Explorer_statMonitor* init_explorer_stat_monitor(Explorer_statData*);
void free_monitor(Explorer_statMonitor*);

/*
 * Monitor Event Handlers
 */
void explorer_stat_retrieved(Explorer_StatMonitor* monitor, int mon_var_move_count);
void raise_explorer_stat_retrieved(Explorer_StatMonitor* monitor, int mon_var_move_count);
void explorer_stat_over_threshold(Explorer_StatMonitor* monitor);
void raise_explorer_stat_over_threshold(Explorer_StatMonitor* monitor);
void raise_explorer_stat_op(Explorer_StatMonitor* monitor, int mon_var_None);

/*
 * Monitor Utility Functions
 */
Explorer_statMonitorRecord* get_explorer_stat_monitors();
Explorer_statMonitorRecord* get_explorer_stat_monitors_by_identity(int, int, void*);
Explorer_statMonitorRecord* filter_explorer_stat_monitors_by_identity(Explorer_statMonitorRecord*, int, void*);
int init_explorer_stat_monitor_maps();
void free_explorer_stat_monitor_maps();
int add_explorer_stat_monitor_to_map(Explorer_statMonitor*, int);
int put_explorer_stat_monitor(Explorer_statMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);