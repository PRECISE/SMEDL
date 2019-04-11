#ifndef {{ base_file_name|upper }}_MONITOR_WRAPPER_H
#define {{ base_file_name|upper }}_MONITOR_WRAPPER_H

#define {{ obj|upper }}_MONITOR_MAP_SIZE 100 // number of buckets
#define {{ obj|upper }}_MONITOR_IDENTITIES {{ identities|length }}

typedef struct {{ obj|title }}MonitorRecord {
  {{ obj|title }}Monitor *monitor;
  struct {{ obj|title }}MonitorRecord *next;
  struct {{ obj|title }}MonitorRecord *left;
  struct {{ obj|title }}MonitorRecord *right;
} {{ obj|title }}MonitorRecord;

typedef struct {{ obj|title }}MonitorMap {
  {{ obj|title }}MonitorRecord *list[{{ obj|upper }}_MONITOR_MAP_SIZE];
} {{ obj|title }}MonitorMap;

{{ obj|title }}MonitorMap* {{ obj|lower }}_monitor_maps[{{ obj|upper }}_MONITOR_IDENTITIES]; //a map for each identity
pthread_mutex_t {{ obj|lower }}_monitor_maps_lock;

// Called by the global wrapper to handle incoming events. It dispatches them to the appropriate instance
// and performs dynamic instantiation if necessary.
// The first 4 parameters align with get_{{ obj|lower }}_monitors_by_identities. If there are no identities to match,
// they should be NULL, 0, NULL, 0 (although it doesn't really matter).
// event_id is from the {{ obj|lower }}_event enum
// params are the parameters of the event
void import_event_{{ obj|lower }}(int identity[], int type, void *values[], int size, int event_id, param *params);

// Called by the global wrapper when it needs to export events to RabbitMQ. It calls the appropriate
// exported_<monitortype>_<eventname>() function to generate the JSON and send the message.
void export_async_event_{{ obj|lower }}(MonitorIdentity** identities, int event_id, param *params);

// Monitor instance management changes
int init_{{ obj|lower }}_monitor_maps();
void free_{{ obj|lower }}_monitor_maps();
int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor*); //puts into all maps
void remove_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) ;
int add_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor*, int);
int remove_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity);
void insert_{{ obj|lower }}_record({{ obj|title }}MonitorRecord*, {{ obj|title }}MonitorRecord*, int, int);
{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors();
{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identities(int[], int type, void *[],int);
{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord*, int, void*);
{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors_by_identity(int, int, void*);
{{ obj|title }}MonitorRecord* find_{{ obj|lower }}_record({{ obj|title }}MonitorRecord*, void*, int);
{{ obj|title }}MonitorRecord* traverseAndGet_{{ obj|lower }}({{ obj|title }}MonitorRecord*, int);



#endif //{{ base_file_name|upper }}_MONITOR_WRAPPER_H
