#include "monitor_map.h"
#include "actions.h"
#include <stdio.h> // For the log file
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <pthread.h>

#define POSTER_MONITOR_MAP_SIZE 100 // number of buckets
#define POSTER_MONITOR_IDENTITIES 1

typedef struct PosterData {
  void* id;
  int cur_tracks_out;
  int cur_bytes_in;
  int last_tracks_out;
  int last_bytes_in;
  int cur_time;
  int last_init;
} PosterData;

typedef struct PosterMonitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[1];
  int state[3];
  int cur_tracks_out;
  int cur_bytes_in;
  int last_tracks_out;
  int last_bytes_in;
  int cur_time;
  int last_init;
  action *action_queue;
  FILE *logFile;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
} PosterMonitor;

typedef struct PosterMonitorRecord {
  PosterMonitor *monitor;
  struct PosterMonitorRecord *next;
} PosterMonitorRecord;

typedef struct PosterMonitorMap {
  PosterMonitorRecord *list[POSTER_MONITOR_MAP_SIZE];
} PosterMonitorMap;

PosterMonitorMap* poster_monitor_maps[POSTER_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t poster_monitor_maps_lock;

PosterMonitor* init_poster_monitor(PosterData*);
void free_monitor(PosterMonitor*);

/*
 * Monitor Event Handlers
 */
void poster_consume_input(PosterMonitor* monitor, int mon_var_nbytes);
void raise_poster_consume_input(PosterMonitor* monitor, int mon_var_nbytes);
void poster_produce_tracks(PosterMonitor* monitor, int mon_var_ntracks);
void raise_poster_produce_tracks(PosterMonitor* monitor, int mon_var_ntracks);
void poster_heartbeat(PosterMonitor* monitor, int mon_var_now);
void raise_poster_heartbeat(PosterMonitor* monitor, int mon_var_now);
void raise_poster_too_few_tracks(PosterMonitor* monitor, int mon_var_cur_time);

/*
 * Monitor Utility Functions
 */
PosterMonitorRecord* get_poster_monitors();
PosterMonitorRecord* get_poster_monitors_by_identity(int, int, void*);
PosterMonitorRecord* filter_poster_monitors_by_identity(PosterMonitorRecord*, int, void*);
int init_poster_monitor_maps();
void free_poster_monitor_maps();
int add_poster_monitor_to_map(PosterMonitor*, int);
int put_poster_monitor(PosterMonitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
