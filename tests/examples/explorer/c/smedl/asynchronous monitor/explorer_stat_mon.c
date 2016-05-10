//Compile: gcc -o explorer_stat_mon -L/usr/local/lib -lczmq -I/usr/local/include -std=c99 actions.c monitor_map.c explorer_stat_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "explorer_stat_mon.h"
#include "czmq.h"

typedef enum { EXPLORER_STAT_ID } explorer_stat_identity;
const identity_type explorer_stat_identity_types[EXPLORER_STAT_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { EXPLORER_STAT_STAT_SCENARIO } explorer_stat_scenario;
typedef enum { EXPLORER_STAT_STAT_START } explorer_stat_stat_state;
typedef enum { EXPLORER_STAT_RETRIEVED_EVENT, EXPLORER_STAT_OVER_THRESHOLD_EVENT, EXPLORER_STAT_OP_EVENT } explorer_stat_event;
typedef enum { EXPLORER_STAT_DEFAULT } explorer_stat_error;
const char *explorer_stat_stat_states[1] = { "Start" };
const char **explorer_stat_states_names[1] = { explorer_stat_stat_states };

Explorer_statMonitor* init_explorer_stat_monitor( Explorer_statData *d ) {
    Explorer_statMonitor* monitor = (Explorer_statMonitor*)malloc(sizeof(Explorer_statMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EXPLORER_STAT_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->sum = d->sum;
    monitor->sum_count = d->sum_count;
    monitor->targetNum = d->targetNum;
    monitor->state[EXPLORER_STAT_STAT_SCENARIO] = EXPLORER_STAT_STAT_START;
    monitor->logFile = fopen("Explorer_statMonitor.log", "w");

    monitor->publisher = zsock_new_pub (">tcp://localhost:5559");
    assert (monitor->publisher);
    assert (zsock_resolve (monitor->publisher) != monitor->publisher);
    assert (streq (zsock_type_str (monitor->publisher), "PUB"));

    monitor->subscriber = zsock_new_sub (">tcp://localhost:5560");
    assert (monitor->subscriber);
    assert (zsock_resolve (monitor->subscriber) != monitor->subscriber);
    assert (streq (zsock_type_str (monitor->subscriber), "SUB"));

    put_explorer_stat_monitor(monitor);
    return monitor;
}

static int
event_filter (zloop_t *loop, zsock_t *reader, void *arg)
{
    zmsg_t *msg = zmsg_recv (reader);
    assert (msg);
    char *msg_str = zmsg_popstr (msg);
    printf ("INCOMING_MSG: %s\n", msg_str);

    // TODO: Do filtering here, with Monitor address as one of the arguments so we can call the event handlers

    free (msg_str);
    zmsg_destroy (&msg);
    return 0;
}


void start_monitor(Explorer_statMonitor* monitor) {
    zloop_t *loop = zloop_new ();
    assert (loop);
    zloop_set_verbose (loop, verbose);

    int rc = zloop_reader (loop, monitor->subscriber, event_filter, NULL);
    assert (rc == 0);
    zloop_reader_set_tolerant (loop, input);
    zloop_start (loop);
    // Looping continues until interrupted
    zloop_destroy (&loop);
    assert (loop == NULL);
}

void free_monitor(Explorer_statMonitor* monitor) {
    zsock_destroy(&monitor->publisher);
    zsock_destroy(&monitor->subscriber);
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void explorer_stat_retrieved(Explorer_StatMonitor* monitor, int mon_var_move_count) {
  switch (monitor->state[EXPLORER_STAT_STAT_SCENARIO]) {
    case EXPLORER_STAT_STAT_START:
        monitor->sum = monitor->sum + 1;
        monitor->sum_count = monitor->sum_count + mon_var_move_count;
      monitor->state[EXPLORER_STAT_STAT_SCENARIO] = EXPLORER_STAT_STAT_START;
      break;

  }
}

void raise_explorer_stat_retrieved(Explorer_StatMonitor* monitor, int mon_var_move_count) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_move_count, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_STAT_RETRIEVED_EVENT, p_head);
}


void explorer_stat_over_threshold(Explorer_StatMonitor* monitor) {
  switch (monitor->state[EXPLORER_STAT_STAT_SCENARIO]) {
    case EXPLORER_STAT_STAT_START:
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: op; Event parameters : "); }
        monitor->sum_count = 0;
      monitor->state[EXPLORER_STAT_STAT_SCENARIO] = EXPLORER_STAT_STAT_START;
      break;

  }
}

void raise_explorer_stat_over_threshold(Explorer_StatMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORER_STAT_OVER_THRESHOLD_EVENT, p_head);
}




void raise_explorer_stat_op(Explorer_StatMonitor* monitor, int mon_var_None) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_None, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORER_STAT_OP_EVENT, p_head);

  // Export event to external monitors
  char str[60];
  //sprintf(str, "/explorer/%d/retrieved  %d", monitor->identities[EXPLORER_ID]->value, mon_var_move_count);
  sprintf(str, "/explorer/1/op  %d", mon_var_None);
  zstr_send (monitor->publisher, str);
}


/*
 * Monitor Utility Functions
 */

int init_explorer_stat_monitor_maps() {
    if (pthread_mutex_init(&explorer_stat_monitor_maps_lock, NULL) != 0) {
        printf("\nExplorer_stat Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < EXPLORER_STAT_MONITOR_IDENTITIES; i++) {
        explorer_stat_monitor_maps[i] = (Explorer_statMonitorMap*)malloc(sizeof(Explorer_statMonitorMap));
    }
    return 1;
}

void free_explorer_stat_monitor_maps() {
    // TODO
}

int add_explorer_stat_monitor_to_map(Explorer_statMonitor *monitor, int identity) {
    Explorer_statMonitorMap* map = explorer_stat_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, EXPLORER_STAT_MONITOR_MAP_SIZE);
    Explorer_statMonitorRecord* record = (Explorer_statMonitorRecord*)malloc(sizeof(Explorer_statMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&explorer_stat_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&explorer_stat_monitor_maps_lock);
    return 1;
}

int put_explorer_stat_monitor(Explorer_statMonitor *monitor) {
    return add_explorer_stat_monitor_to_map(monitor, EXPLORER_STAT_ID);
}

Explorer_statMonitorRecord* get_explorer_stat_monitors() {
    Explorer_statMonitorRecord* results = NULL;
    Explorer_statMonitorMap* map = explorer_stat_monitor_maps[0];
    for(int i = 0; i < EXPLORER_STAT_MONITOR_MAP_SIZE; i++) {
        Explorer_statMonitorRecord* current = map->list[i];
        while(current != NULL) {
            Explorer_statMonitorRecord* record = (Explorer_statMonitorRecord*)malloc(sizeof(Explorer_statMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

Explorer_statMonitorRecord* get_explorer_stat_monitors_by_identity(int identity, int type, void *value) {
    Explorer_statMonitorRecord* results = NULL;
    Explorer_statMonitorMap* map = explorer_stat_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, EXPLORER_STAT_MONITOR_MAP_SIZE);
    Explorer_statMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            Explorer_statMonitorRecord* record = (Explorer_statMonitorRecord*)malloc(sizeof(Explorer_statMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

Explorer_statMonitorRecord* filter_explorer_stat_monitors_by_identity(Explorer_statMonitorRecord* before, int identity, void  *value) {
    Explorer_statMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            Explorer_statMonitorRecord* record = (Explorer_statMonitorRecord*)malloc(sizeof(Explorer_statMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}\n", scen, state, action, type);
}