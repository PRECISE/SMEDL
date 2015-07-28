#include "monitor_map.h"

#define CAR_MONITOR_MAP_SIZE 100 // number of buckets
#define CAR_MONITOR_IDENTITIES 1

typedef struct CarMonitor {
  pthread_mutex_t monitor_lock;   
  MonitorIdentity *identities[1];
  int laps;
  int total;
} CarMonitor;

typedef struct CarMonitorRecord {
  CarMonitor *monitor;
  struct CarMonitorRecord *next; // next node in the list
} CarMonitorRecord;

typedef struct CarMonitorMap {
  CarMonitorRecord *list[CAR_MONITOR_MAP_SIZE]; // "buckets" of linked lists
} CarMonitorMap;

CarMonitorMap* car_monitor_maps[CAR_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t car_monitor_maps_lock;

/* Function prototypes */
CarMonitor* init_car_monitor(pthread_t*);
int init_car_monitor_maps();
int add_car_monitor_to_map(CarMonitor*, int);
int put_car_monitor(CarMonitor*); //puts into all maps
CarMonitorRecord* get_car_monitors();
CarMonitorRecord* get_car_monitors_by_identity(int, int, void*);
CarMonitorRecord* filter_car_monitors_by_identity(CarMonitorRecord*, int, void*);
// void init_car_monitor_store();
// void free_car_monitor_store();