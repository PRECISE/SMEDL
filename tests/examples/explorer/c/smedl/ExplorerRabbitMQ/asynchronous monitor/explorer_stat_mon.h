#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <pthread.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <assert.h>

//#include <czmq.h>


#define EXPLORERSTAT_MONITOR_MAP_SIZE 100 // number of buckets
#define EXPLORERSTAT_MONITOR_IDENTITIES 1

typedef struct ExplorerstatData {
  void* id;
  int sum;
  int count;
  int targetNum;
} ExplorerstatData;

typedef struct ExplorerstatMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[2];
  int sum;
  int count;
  int targetNum;
  action *action_queue;
  FILE *logFile;
   // zsock_t * publisher;
   // zsock_t * subscriber;
    amqp_socket_t *recv_socket;
    amqp_connection_state_t recv_conn;
 
    amqp_socket_t *send_socket;
    amqp_connection_state_t send_conn;
    
} ExplorerstatMonitor;

typedef struct ExplorerstatMonitorRecord {
  ExplorerstatMonitor *monitor;
  struct ExplorerstatMonitorRecord *next;
} ExplorerstatMonitorRecord;

typedef struct ExplorerstatMonitorMap {
  ExplorerstatMonitorRecord *list[EXPLORERSTAT_MONITOR_MAP_SIZE];
} ExplorerstatMonitorMap;

ExplorerstatMonitorMap* explorerstat_monitor_maps[EXPLORERSTAT_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t explorerstat_monitor_maps_lock;

ExplorerstatMonitor* init_explorerstat_monitor(ExplorerstatData*);
void free_monitor(ExplorerstatMonitor*);

/*
 * Monitor Event Handlers
 */
void explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count);
void raise_explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count);
void explorerstat_reachNum(ExplorerstatMonitor* monitor);
void raise_explorerstat_reachNum(ExplorerstatMonitor* monitor);
void raise_explorerstat_output(ExplorerstatMonitor* monitor, float mon_var_None);

/*
 * Monitor Utility Functions
 */
ExplorerstatMonitorRecord* get_explorerstat_monitors();
ExplorerstatMonitorRecord* get_explorerstat_monitors_by_identity(int, int, void*);
ExplorerstatMonitorRecord* filter_explorerstat_monitors_by_identity(ExplorerstatMonitorRecord*, int, void*);
int init_explorerstat_monitor_maps();
void free_explorerstat_monitor_maps();
int add_explorerstat_monitor_to_map(ExplorerstatMonitor*, int);
int put_explorerstat_monitor(ExplorerstatMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);