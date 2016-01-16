#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define SIMPLEPARSERMON_MONITOR_MAP_SIZE 100 // number of buckets
#define SIMPLEPARSERMON_MONITOR_IDENTITIES 1

typedef struct SimpleparsermonData {  
  void* id;
  int currentTime;
} SimpleparsermonData;

typedef struct SimpleparsermonMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[1];
  int state[3];
  int currentTime;
  action *action_queue;
} SimpleparsermonMonitor;

typedef struct SimpleparsermonMonitorRecord {
  SimpleparsermonMonitor *monitor;
  struct SimpleparsermonMonitorRecord *next;
} SimpleparsermonMonitorRecord;

typedef struct SimpleparsermonMonitorMap {
  SimpleparsermonMonitorRecord *list[SIMPLEPARSERMON_MONITOR_MAP_SIZE];
} SimpleparsermonMonitorMap;

SimpleparsermonMonitorMap* simpleparsermon_monitor_maps[SIMPLEPARSERMON_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t simpleparsermon_monitor_maps_lock;

SimpleparsermonMonitor* init_simpleparsermon_monitor(SimpleparsermonData*);
int init_simpleparsermon_monitor_maps();
int add_simpleparsermon_monitor_to_map(SimpleparsermonMonitor*, int);
int put_simpleparsermon_monitor(SimpleparsermonMonitor*); //puts into all maps
SimpleparsermonMonitorRecord* get_simpleparsermon_monitors();
SimpleparsermonMonitorRecord* get_simpleparsermon_monitors_by_identity(int, int, void*);
SimpleparsermonMonitorRecord* filter_simpleparsermon_monitors_by_identity(SimpleparsermonMonitorRecord*, int, void*);
void simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed);
void simpleparsermon_getSpeed_probe();
void raise_simpleparsermon_getSpeed(SimpleparsermonMonitor* monitor, float speed);
void simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat);
void simpleparsermon_getLat_probe();
void raise_simpleparsermon_getLat(SimpleparsermonMonitor* monitor, float lat);
void simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist);
void simpleparsermon_getDist_probe();
void raise_simpleparsermon_getDist(SimpleparsermonMonitor* monitor, float dist);
void simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time);
void simpleparsermon_getTime_probe();
void raise_simpleparsermon_getTime(SimpleparsermonMonitor* monitor, int time);
void simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon);
void simpleparsermon_getLon_probe();
void raise_simpleparsermon_getLon(SimpleparsermonMonitor* monitor, float lon);
void raise_error(char*, const char*, char*, char*);
void free_simpleparsermon_monitor();
void free_simpleparsermon_monitor_maps();