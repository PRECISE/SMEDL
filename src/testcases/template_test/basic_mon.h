#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define BASIC_MONITOR_MAP_SIZE 100 // number of buckets
#define BASIC_MONITOR_IDENTITIES 2

typedef struct BasicData {  
  int num;
  void* data;
  int y;
  int x;
  int total;
} BasicData;

typedef struct BasicMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[2];
  int state[2];
  int y;
  int x;
  int total;
  action *action_queue;
} BasicMonitor;

typedef struct BasicMonitorRecord {
  BasicMonitor *monitor;
  struct BasicMonitorRecord *next;
} BasicMonitorRecord;

typedef struct BasicMonitorMap {
  BasicMonitorRecord *list[BASIC_MONITOR_MAP_SIZE];
} BasicMonitorMap;

BasicMonitorMap* basic_monitor_maps[BASIC_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t basic_monitor_maps_lock;

BasicMonitor* init_basic_monitor(BasicData*);
int init_basic_monitor_maps();
int add_basic_monitor_to_map(BasicMonitor*, int);
int put_basic_monitor(BasicMonitor*); //puts into all maps
BasicMonitorRecord* get_basic_monitors();
BasicMonitorRecord* get_basic_monitors_by_identity(int, int, void*);
BasicMonitorRecord* filter_basic_monitors_by_identity(BasicMonitorRecord*, int, void*);
void basic_upY(BasicMonitor* monitor);
void basic_upY_probe(void* data, int num);
void raise_basic_upY(BasicMonitor* monitor);
void basic_upX(BasicMonitor* monitor);
void basic_upX_probe(void* data, int num);
void raise_basic_upX(BasicMonitor* monitor);
void basic_upTotal(BasicMonitor* monitor, int x);
void raise_basic_upTotal(BasicMonitor* monitor, int x);
void raise_error(char*, const char*, char*, char*);
void free_basic_monitor();
void free_basic_monitor_maps();