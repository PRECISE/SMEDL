#include "monitor_map.h"
#include "actions.h"
#include <pthread.h>

#define TABMON_MONITOR_MAP_SIZE 100 // number of buckets
#define TABMON_MONITOR_IDENTITIES 2

typedef struct TabmonData {
  void* id;
  void* test;
  URL currentUrl;
  URL testUrl;
  Renderer rengine;
} TabmonData;

typedef struct TabmonMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[2];
  int state[2];
  URL currentUrl;
  URL testUrl;
  Renderer rengine;
  action *action_queue;
} TabmonMonitor;

typedef struct TabmonMonitorRecord {
  TabmonMonitor *monitor;
  struct TabmonMonitorRecord *next;
} TabmonMonitorRecord;

typedef struct TabmonMonitorMap {
  TabmonMonitorRecord *list[TABMON_MONITOR_MAP_SIZE];
} TabmonMonitorMap;

TabmonMonitorMap* tabmon_monitor_maps[TABMON_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t tabmon_monitor_maps_lock;

TabmonMonitor* init_tabmon_monitor(TabmonData*);

/*
 * Monitor Event Handlers
 */
void tabmon_store(TabmonMonitor* monitor, Tab this, Cookie cookie);
void raise_tabmon_store(TabmonMonitor* monitor, Tab this, Cookie cookie);
void tabmon_render(TabmonMonitor* monitor, Renderer rengine, URL url);
void raise_tabmon_render(TabmonMonitor* monitor, Renderer rengine, URL url);
void tabmon_displayUrl(TabmonMonitor* monitor, Tab this, URL url);
void raise_tabmon_displayUrl(TabmonMonitor* monitor, Tab this, URL url);
void tabmon_cookieIntegrityAlarm(TabmonMonitor* monitor);
void raise_tabmon_cookieIntegrityAlarm(TabmonMonitor* monitor);

/*
 * Monitor Utility Functions
 */
TabmonMonitorRecord* get_tabmon_monitors();
TabmonMonitorRecord* get_tabmon_monitors_by_identity(int, int, void*);
TabmonMonitorRecord* filter_tabmon_monitors_by_identity(TabmonMonitorRecord*, int, void*);
int init_tabmon_monitor_maps();
int add_tabmon_monitor_to_map(TabmonMonitor*, int);
int put_tabmon_monitor(TabmonMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
void free_tabmon_monitor();
void free_tabmon_monitor_maps();