//Compile: gcc -o explorer_stat_mon -std=c99 actions.c monitor_map.c explorer_stat_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "explorer_stat_mon.h"
#include <czmq.h>

typedef enum { EXPLORERSTAT_ID } explorerstat_identity;
const identity_type explorerstat_identity_types[EXPLORERSTAT_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { EXPLORERSTAT_STAT_SCENARIO, EXPLORERSTAT_CHECK_SCENARIO } explorerstat_scenario;
typedef enum { EXPLORERSTAT_STAT_START } explorerstat_stat_state;
typedef enum { EXPLORERSTAT_CHECK_CHECKSUM } explorerstat_check_state;
typedef enum { EXPLORERSTAT_RETRIEVED_EVENT, EXPLORERSTAT_REACHNUM_EVENT, EXPLORERSTAT_OUTPUT_EVENT } explorerstat_event;
typedef enum { EXPLORERSTAT_DEFAULT } explorerstat_error;
const char *explorerstat_stat_states[1] = { "Start" };
const char *explorerstat_check_states[1] = { "CheckSum" };
const char **explorerstat_states_names[2] = { explorerstat_stat_states, explorerstat_check_states };

ExplorerstatMonitor* mon1 = NULL;


ExplorerstatMonitor* init_explorerstat_monitor( ExplorerstatData *d ) {
    ExplorerstatMonitor* monitor = (ExplorerstatMonitor*)malloc(sizeof(ExplorerstatMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EXPLORERSTAT_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->sum = d->sum;
    monitor->count = d->count;
    monitor->targetNum = d->targetNum;
    monitor->state[EXPLORERSTAT_STAT_SCENARIO] = EXPLORERSTAT_STAT_START;
    monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
    monitor->logFile = fopen("ExplorerstatMonitor.log", "w");
    
    monitor->publisher = zsock_new_pub (">tcp://localhost:5559");
    assert (monitor->publisher);
    assert (zsock_resolve (monitor->publisher) != monitor->publisher);
    assert (streq (zsock_type_str (monitor->publisher), "PUB"));
    
    monitor->subscriber = zsock_new_sub (">tcp://localhost:5560","");
    assert (monitor->subscriber);
    assert (zsock_resolve (monitor->subscriber) != monitor->subscriber);
    assert (streq (zsock_type_str (monitor->subscriber), "SUB"));
    
    put_explorerstat_monitor(monitor);
    mon1 = monitor;
    return monitor;
}

int getParameterOfRetrieved(char* eventName, char * msg){
    if(strstr(msg,eventName)==NULL){
        return -1;
    }
    if(msg != NULL){
        int position = 0;
        for(position =0;position<strlen(msg);position++){
            if(msg[position]==' '){
                break;
            }
        }
        while(position < strlen(msg)){
            if(msg[position]!=' '){
                break;
            }
            position++;
        }
        if(position != strlen(msg)){
            char intString[15] = {};
            int k = 0;
            for(int i = position;i<strlen(msg);i++){
                intString[k++] = msg[i];
            }
            intString[k]='\0';
            return atoi(intString);
        }
    }
    return -1;
}

static int
event_filter (zloop_t *loop, zsock_t *reader, void *arg)
{
    zmsg_t *msg = zmsg_recv (reader);
    assert (msg);
    char *msg_str = zmsg_popstr (msg);
    printf ("INCOMING_MSG: %s\n", msg_str);
    
    // TODO: Do filtering here, with Monitor address as one of the arguments so we can call the event handlers
    
    int moveCount = getParameterOfRetrieved("retrieved",msg_str);
    if(moveCount >= 0){
        explorerstat_retrieved(mon1,moveCount);
    }
    
    free (msg_str);
    zmsg_destroy (&msg);
    return 0;
}

void start_monitor(ExplorerstatMonitor* monitor) {
    bool verbose = true;
    zloop_t *loop = zloop_new ();
    assert (loop);
    zloop_set_verbose (loop, verbose);
    
    int rc = zloop_reader (loop, monitor->subscriber, event_filter, NULL);
    assert (rc == 0);
    zloop_reader_set_tolerant (loop, event_filter);
    zloop_start (loop);
    // Looping continues until interrupted
    zloop_destroy (&loop);
    assert (loop == NULL);
}

void free_monitor(ExplorerstatMonitor* monitor) {
    zsock_destroy(&monitor->publisher);
    zsock_destroy(&monitor->subscriber);
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count) {
  switch (monitor->state[EXPLORERSTAT_STAT_SCENARIO]) {
    case EXPLORERSTAT_STAT_START:
        monitor->sum = monitor->sum + 1;
        monitor->count = monitor->count + mon_var_move_count;
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: reachNum; Event parameters : "); }
      monitor->state[EXPLORERSTAT_STAT_SCENARIO] = EXPLORERSTAT_STAT_START;
          explorerstat_reachNum(monitor);
      break;

  }
}

void raise_explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_move_count, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORERSTAT_RETRIEVED_EVENT, p_head);
}


void explorerstat_reachNum(ExplorerstatMonitor* monitor) {
  switch (monitor->state[EXPLORERSTAT_CHECK_SCENARIO]) {
    case EXPLORERSTAT_CHECK_CHECKSUM:
      if(monitor->sum < monitor->targetNum) {
        monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
      }
      else {
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: output; Event parameters : "); }
          printf("count:%d,sum:%d\n",monitor->count,monitor->sum);
          int tempsum = monitor -> sum;
          int tempcount = monitor -> count;
        monitor->sum = 0;
        monitor->count = 0;
        monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
          raise_explorerstat_output(monitor,(tempcount+0.0)/tempsum);

      }
      break;

  }
}

void raise_explorerstat_reachNum(ExplorerstatMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORERSTAT_REACHNUM_EVENT, p_head);
}



void raise_explorerstat_output(ExplorerstatMonitor* monitor, float mon_var_None) {
    printf("mon_var_None:%f\n",mon_var_None);
    param *p_head = NULL;
    push_param(&p_head, &mon_var_None, NULL, NULL, NULL);
    push_action(&monitor->action_queue, EXPLORERSTAT_OUTPUT_EVENT, p_head);
    
    // Export event to external monitors
    char str[60];
    //sprintf(str, "/explorer/%d/retrieved  %d", monitor->identities[EXPLORER_ID]->value, mon_var_move_count);
    sprintf(str, "/explorer/1/output  %f", mon_var_None);
    zstr_send (monitor->publisher, str);
    printf("msum:%d,mcount:%d\n",monitor->sum,monitor->count);
    
}


/*
 * Monitor Utility Functions
 */

int init_explorerstat_monitor_maps() {
    if (pthread_mutex_init(&explorerstat_monitor_maps_lock, NULL) != 0) {
        printf("\nExplorerstat Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < EXPLORERSTAT_MONITOR_IDENTITIES; i++) {
        explorerstat_monitor_maps[i] = (ExplorerstatMonitorMap*)malloc(sizeof(ExplorerstatMonitorMap));
    }
    return 1;
}

void free_explorerstat_monitor_maps() {
    // TODO
}

int add_explorerstat_monitor_to_map(ExplorerstatMonitor *monitor, int identity) {
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, EXPLORERSTAT_MONITOR_MAP_SIZE);
    ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&explorerstat_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&explorerstat_monitor_maps_lock);
    return 1;
}

int put_explorerstat_monitor(ExplorerstatMonitor *monitor) {
    return add_explorerstat_monitor_to_map(monitor, EXPLORERSTAT_ID);
}

ExplorerstatMonitorRecord* get_explorerstat_monitors() {
    ExplorerstatMonitorRecord* results = NULL;
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[0];
    for(int i = 0; i < EXPLORERSTAT_MONITOR_MAP_SIZE; i++) {
        ExplorerstatMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ExplorerstatMonitorRecord* get_explorerstat_monitors_by_identity(int identity, int type, void *value) {
    ExplorerstatMonitorRecord* results = NULL;
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, EXPLORERSTAT_MONITOR_MAP_SIZE);
    ExplorerstatMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ExplorerstatMonitorRecord* filter_explorerstat_monitors_by_identity(ExplorerstatMonitorRecord* before, int identity, void  *value) {
    ExplorerstatMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
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