#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define THRESHOLDCROSSDETECTION_MONITOR_MAP_SIZE 100 // number of buckets
#define THRESHOLDCROSSDETECTION_MONITOR_IDENTITIES 1

typedef struct ThresholdcrossdetectionData {
  int id;
  double xingTime;
  double threshold;
  double holdTime;
  char* name;
  int trigger;
} ThresholdcrossdetectionData;

typedef struct ThresholdcrossdetectionMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[1];
  double xingTime;
  double threshold;
  double holdTime;
  char* name;
  int trigger;
  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} ThresholdcrossdetectionMonitor;

typedef struct ThresholdcrossdetectionMonitorRecord {
  ThresholdcrossdetectionMonitor *monitor;
  struct ThresholdcrossdetectionMonitorRecord *next;
} ThresholdcrossdetectionMonitorRecord;

typedef struct ThresholdcrossdetectionMonitorMap {
  ThresholdcrossdetectionMonitorRecord *list[THRESHOLDCROSSDETECTION_MONITOR_MAP_SIZE];
} ThresholdcrossdetectionMonitorMap;

ThresholdcrossdetectionMonitorMap* thresholdcrossdetection_monitor_maps[THRESHOLDCROSSDETECTION_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t thresholdcrossdetection_monitor_maps_lock;

ThresholdcrossdetectionMonitor* init_thresholdcrossdetection_monitor(ThresholdcrossdetectionData*);
void start_monitor(ThresholdcrossdetectionMonitor* monitor);
void free_monitor(ThresholdcrossdetectionMonitor*);

/*
 * Monitor Event Handlers
 */
void thresholdcrossdetection_dataUpdate(ThresholdcrossdetectionMonitor* monitor, char* n, double ts, double val, smedl_provenance_t* provenance);
void raise_thresholdcrossdetection_dataUpdate(ThresholdcrossdetectionMonitor* monitor, char* v0, double v1, double v2, smedl_provenance_t* provenance);
void thresholdcrossdetection_timeout(ThresholdcrossdetectionMonitor* monitor, smedl_provenance_t* provenance);
void raise_thresholdcrossdetection_timeout(ThresholdcrossdetectionMonitor* monitor, smedl_provenance_t* provenance);
void thresholdcrossdetection_thresholdWarning(ThresholdcrossdetectionMonitor* monitor, char* name, int trigger, smedl_provenance_t* provenance);
void exported_thresholdcrossdetection_thresholdWarning(ThresholdcrossdetectionMonitor* monitor , char* v0, int v1, smedl_provenance_t* provenance);
void raise_thresholdcrossdetection_thresholdWarning(ThresholdcrossdetectionMonitor* monitor, char* v0, int v1, smedl_provenance_t* provenance);

/*
 * Monitor Utility Functions
 */
ThresholdcrossdetectionMonitorRecord* get_thresholdcrossdetection_monitors();
ThresholdcrossdetectionMonitorRecord* get_thresholdcrossdetection_monitors_by_identity(int, int, void*);
ThresholdcrossdetectionMonitorRecord* filter_thresholdcrossdetection_monitors_by_identity(ThresholdcrossdetectionMonitorRecord*, int, void*);
int init_thresholdcrossdetection_monitor_maps();
void free_thresholdcrossdetection_monitor_maps();
int add_thresholdcrossdetection_monitor_to_map(ThresholdcrossdetectionMonitor*, int);
int put_thresholdcrossdetection_monitor(ThresholdcrossdetectionMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents(ThresholdcrossdetectionMonitor* monitor);
void executeEvents(ThresholdcrossdetectionMonitor* monitor);
void executeExportedEvent(ThresholdcrossdetectionMonitor* monitor);