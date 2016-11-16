#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define RATECOMPUTATION_MONITOR_MAP_SIZE 100 // number of buckets
#define RATECOMPUTATION_MONITOR_IDENTITIES 1

typedef struct RatecomputationData {
  int id;
  double lastTime;
  double curTime;
  double sum;
  char* name;
  double rate;
} RatecomputationData;

typedef struct RatecomputationMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  double lastTime;
  double curTime;
  double sum;
  char* name;
  double rate;
  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} RatecomputationMonitor;

typedef struct RatecomputationMonitorRecord {
  RatecomputationMonitor *monitor;
  struct RatecomputationMonitorRecord *next;
} RatecomputationMonitorRecord;

typedef struct RatecomputationMonitorMap {
  RatecomputationMonitorRecord *list[RATECOMPUTATION_MONITOR_MAP_SIZE];
} RatecomputationMonitorMap;

RatecomputationMonitorMap* ratecomputation_monitor_maps[RATECOMPUTATION_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t ratecomputation_monitor_maps_lock;

RatecomputationMonitor* init_ratecomputation_monitor(RatecomputationData*);
void start_monitor(RatecomputationMonitor* monitor);
void free_monitor(RatecomputationMonitor*);

/*
 * Monitor Event Handlers
 */
void ratecomputation_dataUpdate(RatecomputationMonitor* monitor, char* metric, double ts, double val);
void raise_ratecomputation_dataUpdate(RatecomputationMonitor* monitor, char* v0, double v1, double v2);
void ratecomputation_timeout(RatecomputationMonitor* monitor);
void raise_ratecomputation_timeout(RatecomputationMonitor* monitor);
void ratecomputation_end(RatecomputationMonitor* monitor);
void raise_ratecomputation_end(RatecomputationMonitor* monitor);
void ratecomputation_dataUpdate2(RatecomputationMonitor* monitor, char* name, double curTime, double rate);
void exported_ratecomputation_dataUpdate2(RatecomputationMonitor* monitor , char* v0, double v1, double v2);
void raise_ratecomputation_dataUpdate2(RatecomputationMonitor* monitor, char* v0, double v1, double v2);

/*
 * Monitor Utility Functions
 */
RatecomputationMonitorRecord* get_ratecomputation_monitors();
RatecomputationMonitorRecord* get_ratecomputation_monitors_by_identity(int, int, void*);
RatecomputationMonitorRecord* filter_ratecomputation_monitors_by_identity(RatecomputationMonitorRecord*, int, void*);
int init_ratecomputation_monitor_maps();
void free_ratecomputation_monitor_maps();
int add_ratecomputation_monitor_to_map(RatecomputationMonitor*, int);
int put_ratecomputation_monitor(RatecomputationMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(RatecomputationMonitor* monitor);
void executeEvents(RatecomputationMonitor* monitor);
void executeExportedEvent(RatecomputationMonitor* monitor);