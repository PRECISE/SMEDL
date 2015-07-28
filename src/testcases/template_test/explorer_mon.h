#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define EXPLORER_MONITOR_MAP_SIZE 100 // number of buckets
#define EXPLORER_MONITOR_IDENTITIES 4

typedef struct ExplorerData {  
  pthread_t thr_id;
  int first_id;
  void* thing_ptr;
  int second_id;
  void* explorer_view;
  int x;
  int interest_threshold;
  int y;
  int heading;
} ExplorerData;

typedef struct ExplorerMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[4];
  int state[2];
  void* explorer_view;
  int x;
  int interest_threshold;
  int y;
  int heading;
  action *action_queue;
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
int init_explorer_monitor_maps();
int add_explorer_monitor_to_map(ExplorerMonitor*, int);
int put_explorer_monitor(ExplorerMonitor*); //puts into all maps
ExplorerMonitorRecord* get_explorer_monitors();
ExplorerMonitorRecord* get_explorer_monitors_by_identity(int, int, void*);
ExplorerMonitorRecord* filter_explorer_monitors_by_identity(ExplorerMonitorRecord*, int, void*);
void raise_error(char*, const char*, char*, char*);
void free_explorer_monitor();
void free_explorer_monitor_maps();