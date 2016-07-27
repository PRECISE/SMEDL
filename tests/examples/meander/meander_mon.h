#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define SAFEMONOBJ_MONITOR_MAP_SIZE 100 // number of buckets
#define SAFEMONOBJ_MONITOR_IDENTITIES 1

typedef struct SafemonobjData {
  void* id;
  int upbound;
  int lobound;
} SafemonobjData;

typedef struct SafemonobjMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[2];
  int upbound;
  int lobound;
  action *action_queue;
  const char *amqp_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} SafemonobjMonitor;

typedef struct SafemonobjMonitorRecord {
  SafemonobjMonitor *monitor;
  struct SafemonobjMonitorRecord *next;
} SafemonobjMonitorRecord;

typedef struct SafemonobjMonitorMap {
  SafemonobjMonitorRecord *list[SAFEMONOBJ_MONITOR_MAP_SIZE];
} SafemonobjMonitorMap;

SafemonobjMonitorMap* safemonobj_monitor_maps[SAFEMONOBJ_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t safemonobj_monitor_maps_lock;

SafemonobjMonitor* init_safemonobj_monitor(SafemonobjData*);
void start_monitor(SafemonobjMonitor* monitor);
void free_monitor(SafemonobjMonitor*);

/*
 * Monitor Event Handlers
 */
void safemonobj_updatePos(SafemonobjMonitor* monitor, int mon_var_pos);
void safemonobj_updatePos_probe(int mon_var_pos);
void raise_safemonobj_updatePos(SafemonobjMonitor* monitor, int mon_var_pos);
void safemonobj_changeDir(SafemonobjMonitor* monitor);
void safemonobj_changeDir_probe();
void raise_safemonobj_changeDir(SafemonobjMonitor* monitor);
void safemonobj_click(SafemonobjMonitor* monitor);
void raise_safemonobj_click(SafemonobjMonitor* monitor);

/*
 * Monitor Utility Functions
 */
SafemonobjMonitorRecord* get_safemonobj_monitors();
SafemonobjMonitorRecord* get_safemonobj_monitors_by_identity(int, int, void*);
SafemonobjMonitorRecord* filter_safemonobj_monitors_by_identity(SafemonobjMonitorRecord*, int, void*);
int init_safemonobj_monitor_maps();
void free_safemonobj_monitor_maps();
int add_safemonobj_monitor_to_map(SafemonobjMonitor*, int);
int put_safemonobj_monitor(SafemonobjMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
