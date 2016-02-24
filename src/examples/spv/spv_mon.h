#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define SPV_MONITOR_MAP_SIZE 100 // number of buckets
#define SPV_MONITOR_IDENTITIES 1

typedef struct SpvData {
  void* id;
  int last_time;
} SpvData;

typedef struct SpvMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[2];
  int last_time;
  action *action_queue;
} SpvMonitor;

typedef struct SpvMonitorRecord {
  SpvMonitor *monitor;
  struct SpvMonitorRecord *next;
} SpvMonitorRecord;

typedef struct SpvMonitorMap {
  SpvMonitorRecord *list[SPV_MONITOR_MAP_SIZE];
} SpvMonitorMap;

SpvMonitorMap* spv_monitor_maps[SPV_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t spv_monitor_maps_lock;

SpvMonitor* init_spv_monitor(SpvData*);

/*
 * Monitor Event Handlers
 */
void spv_parse_record(SpvMonitor* monitor, int time, float lat, float lon, int ret);
void raise_spv_parse_record(SpvMonitor* monitor, int time, float lat, float lon, int ret);
void spv_timestep_error(SpvMonitor* monitor, int time, int last_time);
void raise_spv_timestep_error(SpvMonitor* monitor, int time, int last_time);

/*
 * Monitor Utility Functions
 */
SpvMonitorRecord* get_spv_monitors();
SpvMonitorRecord* get_spv_monitors_by_identity(int, int, void*);
SpvMonitorRecord* filter_spv_monitors_by_identity(SpvMonitorRecord*, int, void*);
int init_spv_monitor_maps();
int add_spv_monitor_to_map(SpvMonitor*, int);
int put_spv_monitor(SpvMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_spv_monitor();
void free_spv_monitor_maps();