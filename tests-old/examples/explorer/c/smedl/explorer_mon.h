#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <pthread.h>
#include "czmq.h"


#define EXPLORER_MONITOR_MAP_SIZE 100 // number of buckets
#define EXPLORER_MONITOR_IDENTITIES 1

typedef struct ExplorerData {
  void* id;
  int mon_x;
  int mon_y;
  int mon_heading;
  int interest_threshold;
  int move_count;
} ExplorerData;

typedef struct ExplorerMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[3];
  int mon_x;
  int mon_y;
  int mon_heading;
  int interest_threshold;
  int move_count;
  action *action_queue;
  FILE *logFile;
  //zsock_t *publisher;
  int callTime;
} ExplorerMonitor;

typedef struct ExplorerMonitorRecord {
  ExplorerMonitor *monitor;
  struct ExplorerMonitorRecord *next;
} ExplorerMonitorRecord;

typedef struct ExplorerMonitorMap {
  ExplorerMonitorRecord *list[EXPLORER_MONITOR_MAP_SIZE];
} ExplorerMonitorMap;

ExplorerMonitorMap* explorer_monitor_maps[EXPLORER_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t explorer_monitor_maps_lock;

ExplorerMonitor* init_explorer_monitor(ExplorerData*);
void free_monitor(ExplorerMonitor*);

/*
 * Monitor Event Handlers
 */
void explorer_view(ExplorerMonitor* monitor, void* mon_var_view_pointer);
void raise_explorer_view(ExplorerMonitor* monitor, void* mon_var_view_pointer);
void explorer_drive(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y, int mon_var_heading, void * map);
void explorer_drive_probe(void* id, int mon_var_x, int mon_var_y, int mon_var_heading, void * map);
void raise_explorer_drive(ExplorerMonitor* monitor, int mon_var_x, int mon_var_y, int mon_var_heading, void * map);
void explorer_turn(ExplorerMonitor* monitor, int mon_var_facing);
void raise_explorer_turn(ExplorerMonitor* monitor, int mon_var_facing);
void explorer_count(ExplorerMonitor* monitor);
void raise_explorer_count(ExplorerMonitor* monitor);
void explorer_found(ExplorerMonitor* monitor);
void raise_explorer_found(ExplorerMonitor* monitor);
void raise_explorer_retrieved(ExplorerMonitor* monitor, int mon_var_move_count);

/*
 * Monitor Utility Functions
 */
ExplorerMonitorRecord* get_explorer_monitors();
ExplorerMonitorRecord* get_explorer_monitors_by_identity(int, int, void*);
ExplorerMonitorRecord* filter_explorer_monitors_by_identity(ExplorerMonitorRecord*, int, void*);
int init_explorer_monitor_maps();
void free_explorer_monitor_maps();
int add_explorer_monitor_to_map(ExplorerMonitor*, int);
int put_explorer_monitor(ExplorerMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);


pthread_mutex_t pub_lock;
zsock_t *head_publisher;