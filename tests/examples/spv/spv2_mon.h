#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
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
  int state[1];
  int last_time;
  action *action_queue;
  const char *amqp_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
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
void start_monitor(SpvMonitor* monitor);
void free_monitor(SpvMonitor*);

/*
 * Monitor Event Handlers
 */
void spv_parse_record(SpvMonitor* monitor, int mon_var_time, double mon_var_lat, double mon_var_lon, int mon_var_ret);
void raise_spv_parse_record(SpvMonitor* monitor, int mon_var_time, double mon_var_lat, double mon_var_lon, int mon_var_ret);

/*
 * Monitor Utility Functions
 */
SpvMonitorRecord* get_spv_monitors();
SpvMonitorRecord* get_spv_monitors_by_identity(int, int, void*);
SpvMonitorRecord* filter_spv_monitors_by_identity(SpvMonitorRecord*, int, void*);
int init_spv_monitor_maps();
void free_spv_monitor_maps();
int add_spv_monitor_to_map(SpvMonitor*, int);
int put_spv_monitor(SpvMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
