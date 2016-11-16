#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define STRINGTEST_MONITOR_MAP_SIZE 100 // number of buckets
#define STRINGTEST_MONITOR_IDENTITIES 1

typedef struct StringtestData {
  void* id;

} StringtestData;

typedef struct StringtestMonitor {
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
} StringtestMonitor;

typedef struct StringtestMonitorRecord {
  StringtestMonitor *monitor;
  struct StringtestMonitorRecord *next;
} StringtestMonitorRecord;

typedef struct StringtestMonitorMap {
  StringtestMonitorRecord *list[STRINGTEST_MONITOR_MAP_SIZE];
} StringtestMonitorMap;

StringtestMonitorMap* stringtest_monitor_maps[STRINGTEST_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t stringtest_monitor_maps_lock;

StringtestMonitor* init_stringtest_monitor(StringtestData*);
void start_monitor(StringtestMonitor* monitor);
void free_monitor(StringtestMonitor*);

/*
 * Monitor Event Handlers
 */
void stringtest_ping(StringtestMonitor* monitor, char* st, int x);
void raise_stringtest_ping(StringtestMonitor* monitor ,char* v0,int v1);
void stringtest_pong(StringtestMonitor* monitor, char* st, int x);
void exported_stringtest_pong(StringtestMonitor* monitor ,char* v0,int v1);
void raise_stringtest_pong(StringtestMonitor* monitor ,char* v0,int v1);

/*
 * Monitor Utility Functions
 */
StringtestMonitorRecord* get_stringtest_monitors();
StringtestMonitorRecord* get_stringtest_monitors_by_identity(int, int, void*);
StringtestMonitorRecord* filter_stringtest_monitors_by_identity(StringtestMonitorRecord*, int, void*);
int init_stringtest_monitor_maps();
void free_stringtest_monitor_maps();
int add_stringtest_monitor_to_map(StringtestMonitor*, int);
int put_stringtest_monitor(StringtestMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(StringtestMonitor* monitor);
void executeEvents(StringtestMonitor* monitor);
void executeExportedEvent(StringtestMonitor* monitor);