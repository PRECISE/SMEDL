#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define JSONTEST_MONITOR_MAP_SIZE 100 // number of buckets
#define JSONTEST_MONITOR_IDENTITIES 1

typedef struct JsontestData {
  void* id;

} JsontestData;

typedef struct JsontestMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];

  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} JsontestMonitor;

typedef struct JsontestMonitorRecord {
  JsontestMonitor *monitor;
  struct JsontestMonitorRecord *next;
} JsontestMonitorRecord;

typedef struct JsontestMonitorMap {
  JsontestMonitorRecord *list[JSONTEST_MONITOR_MAP_SIZE];
} JsontestMonitorMap;

JsontestMonitorMap* jsontest_monitor_maps[JSONTEST_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t jsontest_monitor_maps_lock;

JsontestMonitor* init_jsontest_monitor(JsontestData*);
void start_monitor(JsontestMonitor* monitor);
void free_monitor(JsontestMonitor*);

/*
 * Monitor Event Handlers
 */
void jsontest_ping(JsontestMonitor* monitor, char* st, int i, double f, cJSON * provenance);
void raise_jsontest_ping(JsontestMonitor* monitor, char* v0, int v1, double v2, cJSON* provenance);
void jsontest_pong(JsontestMonitor* monitor, double f, int i, char* st, cJSON * provenance);
void exported_jsontest_pong(JsontestMonitor* monitor , double v0, int v1, char* v2, cJSON* provenance);
void raise_jsontest_pong(JsontestMonitor* monitor, double v0, int v1, char* v2, cJSON* provenance);

/*
 * Monitor Utility Functions
 */
JsontestMonitorRecord* get_jsontest_monitors();
JsontestMonitorRecord* get_jsontest_monitors_by_identity(int, int, void*);
JsontestMonitorRecord* filter_jsontest_monitors_by_identity(JsontestMonitorRecord*, int, void*);
int init_jsontest_monitor_maps();
void free_jsontest_monitor_maps();
int add_jsontest_monitor_to_map(JsontestMonitor*, int);
int put_jsontest_monitor(JsontestMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(JsontestMonitor* monitor);
void executeEvents(JsontestMonitor* monitor);
void executeExportedEvent(JsontestMonitor* monitor);