#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define PQUEUE_MONITOR_MAP_SIZE 100 // number of buckets
#define PQUEUE_MONITOR_IDENTITIES 1

typedef struct PqueueData {  
  void* id;
  int p4;
  int p3;
  int p5;
  int p1;
  int p2;
} PqueueData;

typedef struct PqueueMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[1];
  int state[2];
  int p4;
  int p3;
  int p5;
  int p1;
  int p2;
  action *action_queue;
} PqueueMonitor;

typedef struct PqueueMonitorRecord {
  PqueueMonitor *monitor;
  struct PqueueMonitorRecord *next;
} PqueueMonitorRecord;

typedef struct PqueueMonitorMap {
  PqueueMonitorRecord *list[PQUEUE_MONITOR_MAP_SIZE];
} PqueueMonitorMap;

PqueueMonitorMap* pqueue_monitor_maps[PQUEUE_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t pqueue_monitor_maps_lock;

PqueueMonitor* init_pqueue_monitor(PqueueData*);
int init_pqueue_monitor_maps();
int add_pqueue_monitor_to_map(PqueueMonitor*, int);
int put_pqueue_monitor(PqueueMonitor*); //puts into all maps
PqueueMonitorRecord* get_pqueue_monitors();
PqueueMonitorRecord* get_pqueue_monitors_by_identity(int, int, void*);
PqueueMonitorRecord* filter_pqueue_monitors_by_identity(PqueueMonitorRecord*, int, void*);
void pqueue_push(PqueueMonitor* monitor, int x);
void pqueue_push_probe(void* id);
void raise_pqueue_push(PqueueMonitor* monitor, int x);
void pqueue_pop(PqueueMonitor* monitor, int x);
void pqueue_pop_probe(void* id);
void raise_pqueue_pop(PqueueMonitor* monitor, int x);
void raise_error(char*, const char*, char*, char*);
void free_pqueue_monitor();
void free_pqueue_monitor_maps();