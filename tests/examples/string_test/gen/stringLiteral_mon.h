#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define STRINGLITERALTEST_MONITOR_MAP_SIZE 100 // number of buckets
#define STRINGLITERALTEST_MONITOR_IDENTITIES 1

typedef struct StringliteraltestData {
  void* id;
  char* name;
  int value;
} StringliteraltestData;

typedef struct StringliteraltestMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  char* name;
  int value;
  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} StringliteraltestMonitor;

typedef struct StringliteraltestMonitorRecord {
  StringliteraltestMonitor *monitor;
  struct StringliteraltestMonitorRecord *next;
} StringliteraltestMonitorRecord;

typedef struct StringliteraltestMonitorMap {
  StringliteraltestMonitorRecord *list[STRINGLITERALTEST_MONITOR_MAP_SIZE];
} StringliteraltestMonitorMap;

StringliteraltestMonitorMap* stringliteraltest_monitor_maps[STRINGLITERALTEST_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t stringliteraltest_monitor_maps_lock;

StringliteraltestMonitor* init_stringliteraltest_monitor(StringliteraltestData*);
void start_monitor(StringliteraltestMonitor* monitor);
void free_monitor(StringliteraltestMonitor*);

/*
 * Monitor Event Handlers
 */
void stringliteraltest_ping(StringliteraltestMonitor* monitor);
void raise_stringliteraltest_ping(StringliteraltestMonitor* monitor);
void stringliteraltest_pong(StringliteraltestMonitor* monitor, char* v0, int v1);
void exported_stringliteraltest_pong(StringliteraltestMonitor* monitor ,char* v0,int v1);
void raise_stringliteraltest_pong(StringliteraltestMonitor* monitor ,char* v0,int v1);

/*
 * Monitor Utility Functions
 */
StringliteraltestMonitorRecord* get_stringliteraltest_monitors();
StringliteraltestMonitorRecord* get_stringliteraltest_monitors_by_identity(int, int, void*);
StringliteraltestMonitorRecord* filter_stringliteraltest_monitors_by_identity(StringliteraltestMonitorRecord*, int, void*);
int init_stringliteraltest_monitor_maps();
void free_stringliteraltest_monitor_maps();
int add_stringliteraltest_monitor_to_map(StringliteraltestMonitor*, int);
int put_stringliteraltest_monitor(StringliteraltestMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(StringliteraltestMonitor* monitor);
void executeEvents(StringliteraltestMonitor* monitor);
void executeExportedEvent(StringliteraltestMonitor* monitor);