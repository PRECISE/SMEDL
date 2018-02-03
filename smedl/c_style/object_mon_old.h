#include "monitor_map.h"
#include "actions.h"
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
{%- if multithreaded %}{{ '\n' }}#include <pthread.h>{% endif %}

#define {{ obj|upper }}_MONITOR_MAP_SIZE 100 // number of buckets
#define {{ obj|upper }}_MONITOR_IDENTITIES {{ identities|length }}

typedef struct {{ obj|title }}Data {
{{ identity_declarations }}
{{ state_var_declarations }}
} {{ obj|title }}Data;

typedef struct {{ obj|title }}Monitor {
  pthread_mutex_t monitor_lock;
  MonitorIdentity *identities[{{ identities|length }}];
  int state[{{ scenario_names|length }}];
{{ state_var_declarations }}
  action *action_queue;
  action *export_queue;
  const char *amqp_exchange;
  const char *ctrl_exchange;
  amqp_socket_t *recv_socket;
  amqp_connection_state_t recv_conn;
  amqp_socket_t *send_socket;
  amqp_connection_state_t send_conn;
 int recycleFlag;
} {{ obj|title }}Monitor;

typedef struct {{ obj|title }}MonitorRecord {
  {{ obj|title }}Monitor *monitor;
  struct {{ obj|title }}MonitorRecord *next;
} {{ obj|title }}MonitorRecord;

typedef struct {{ obj|title }}MonitorMap {
  {{ obj|title }}MonitorRecord *list[{{ obj|upper }}_MONITOR_MAP_SIZE];
} {{ obj|title }}MonitorMap;

{{ obj|title }}MonitorMap* {{ obj|lower }}_monitor_maps[{{ obj|upper }}_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t {{ obj|lower }}_monitor_maps_lock;

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor({{ obj|title }}Data*);
void start_monitor({{ obj|title }}Monitor* monitor);
void free_monitor({{ obj|title }}Monitor*);

/*
 * Monitor Event Handlers
 */
{{ signatures|join(';\n') }};

/*
 * Monitor Utility Functions
 */
{{ obj|title }}Monitor* getMonitorObject();
void addMonitorObjectToPool({{ obj|title }}MonitorRecord*);
int remove_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity, int flag);
void remove_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) ;

{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors();
{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors_by_identity(int, int, void*);
{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord*, int, void*);
int init_{{ obj|lower }}_monitor_maps();
void free_{{ obj|lower }}_monitor_maps();
int add_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor*, int);
int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor*); //puts into all maps
void raise_error(char*, const char*, char*, char*);
char* monitor_identities_str(MonitorIdentity**);
void executePendingEvents({{obj|title}}Monitor* monitor);
void executeEvents({{obj|title}}Monitor* monitor);
void executeExportedEvent({{obj|title}}Monitor* monitor);
