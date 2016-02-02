#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define WEBSERVERMON_MONITOR_MAP_SIZE 100 // number of buckets
#define WEBSERVERMON_MONITOR_IDENTITIES 1

typedef struct WebservermonData {
  void* id;
  URL url;
  HTTPStatusCode code;
} WebservermonData;

typedef struct WebservermonMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  URL url;
  HTTPStatusCode code;
  action *action_queue;
} WebservermonMonitor;

typedef struct WebservermonMonitorRecord {
  WebservermonMonitor *monitor;
  struct WebservermonMonitorRecord *next;
} WebservermonMonitorRecord;

typedef struct WebservermonMonitorMap {
  WebservermonMonitorRecord *list[WEBSERVERMON_MONITOR_MAP_SIZE];
} WebservermonMonitorMap;

WebservermonMonitorMap* webservermon_monitor_maps[WEBSERVERMON_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t webservermon_monitor_maps_lock;

WebservermonMonitor* init_webservermon_monitor(WebservermonData*);

/*
 * Monitor Event Handlers
 */
void webservermon_request(WebservermonMonitor* monitor, URL url);
void raise_webservermon_request(WebservermonMonitor* monitor, URL url);
void webservermon_response(WebservermonMonitor* monitor, HTTPStatusCode code);
void raise_webservermon_response(WebservermonMonitor* monitor, HTTPStatusCode code);

/*
 * Monitor Utility Functions
 */
WebservermonMonitorRecord* get_webservermon_monitors();
WebservermonMonitorRecord* get_webservermon_monitors_by_identity(int, int, void*);
WebservermonMonitorRecord* filter_webservermon_monitors_by_identity(WebservermonMonitorRecord*, int, void*);
int init_webservermon_monitor_maps();
int add_webservermon_monitor_to_map(WebservermonMonitor*, int);
int put_webservermon_monitor(WebservermonMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_webservermon_monitor();
void free_webservermon_monitor_maps();