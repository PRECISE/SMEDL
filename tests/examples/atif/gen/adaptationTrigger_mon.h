#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define ADAPTATIONTRIGGER_MONITOR_MAP_SIZE 100 // number of buckets
#define ADAPTATIONTRIGGER_MONITOR_IDENTITIES 1

typedef struct AdaptationtriggerData {
  int id;
  int Tw;
  int Tat;
  int Tib;
  int enabled;
  char* TwID;
  char* TatID;
  char* TibID;
} AdaptationtriggerData;

typedef struct AdaptationtriggerMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  int Tw;
  int Tat;
  int Tib;
  int enabled;
  char* TwID;
  char* TatID;
  char* TibID;
  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} AdaptationtriggerMonitor;

typedef struct AdaptationtriggerMonitorRecord {
  AdaptationtriggerMonitor *monitor;
  struct AdaptationtriggerMonitorRecord *next;
} AdaptationtriggerMonitorRecord;

typedef struct AdaptationtriggerMonitorMap {
  AdaptationtriggerMonitorRecord *list[ADAPTATIONTRIGGER_MONITOR_MAP_SIZE];
} AdaptationtriggerMonitorMap;

AdaptationtriggerMonitorMap* adaptationtrigger_monitor_maps[ADAPTATIONTRIGGER_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t adaptationtrigger_monitor_maps_lock;

AdaptationtriggerMonitor* init_adaptationtrigger_monitor(AdaptationtriggerData*);
void start_monitor(AdaptationtriggerMonitor* monitor);
void free_monitor(AdaptationtriggerMonitor*);

/*
 * Monitor Event Handlers
 */
void adaptationtrigger_warningThreshold(AdaptationtriggerMonitor* monitor, char* id, int val);
void raise_adaptationtrigger_warningThreshold(AdaptationtriggerMonitor* monitor ,char* v0,int v1);
void adaptationtrigger_activeTracksThreshold(AdaptationtriggerMonitor* monitor, int val);
void raise_adaptationtrigger_activeTracksThreshold(AdaptationtriggerMonitor* monitor ,int v0);
void adaptationtrigger_inputBytesThreshold(AdaptationtriggerMonitor* monitor, int val);
void raise_adaptationtrigger_inputBytesThreshold(AdaptationtriggerMonitor* monitor ,int v0);
void adaptationtrigger_adaptationComplete(AdaptationtriggerMonitor* monitor);
void raise_adaptationtrigger_adaptationComplete(AdaptationtriggerMonitor* monitor);
void adaptationtrigger_eval(AdaptationtriggerMonitor* monitor);
void raise_adaptationtrigger_eval(AdaptationtriggerMonitor* monitor);
void adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor);
void exported_adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor );
void raise_adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor);

/*
 * Monitor Utility Functions
 */
AdaptationtriggerMonitorRecord* get_adaptationtrigger_monitors();
AdaptationtriggerMonitorRecord* get_adaptationtrigger_monitors_by_identity(int, int, void*);
AdaptationtriggerMonitorRecord* filter_adaptationtrigger_monitors_by_identity(AdaptationtriggerMonitorRecord*, int, void*);
int init_adaptationtrigger_monitor_maps();
void free_adaptationtrigger_monitor_maps();
int add_adaptationtrigger_monitor_to_map(AdaptationtriggerMonitor*, int);
int put_adaptationtrigger_monitor(AdaptationtriggerMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(AdaptationtriggerMonitor* monitor);
void executeEvents(AdaptationtriggerMonitor* monitor);
void executeExportedEvent(AdaptationtriggerMonitor* monitor);