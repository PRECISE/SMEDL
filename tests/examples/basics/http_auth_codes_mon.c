//Compile: gcc -o http_auth_codes_mon -std=c99 actions.c monitor_map.c http_auth_codes_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "http_auth_codes_mon.h"

typedef enum { WEBSERVERMON_ID } webservermon_identity;
const identity_type webservermon_identity_types[WEBSERVERMON_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { WEBSERVERMON_AUTHENTICATION_SCENARIO } webservermon_scenario;
typedef enum { WEBSERVERMON_AUTHENTICATION_WEBSERVER, WEBSERVERMON_AUTHENTICATION_GEN0 } webservermon_authentication_state;
typedef enum { WEBSERVERMON_REQUEST_EVENT, WEBSERVERMON_RESPONSE_EVENT } webservermon_event;
typedef enum { WEBSERVERMON_DEFAULT } webservermon_error;
const char *webservermon_authentication_states[2] = { "WebServer", "Gen0" };
const char **webservermon_states_names[1] = { webservermon_authentication_states };

WebservermonMonitor* init_webservermon_monitor( WebservermonData *d ) {
    WebservermonMonitor* monitor = (WebservermonMonitor*)malloc(sizeof(WebservermonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[WEBSERVERMON_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->url = d->url;
    monitor->code = d->code;
    monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO] = WEBSERVERMON_AUTHENTICATION_WEBSERVER;
    put_webservermon_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void webservermon_request(WebservermonMonitor* monitor, URL url) {
  switch (monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO]) {
    case WEBSERVERMON_AUTHENTICATION_WEBSERVER:
      if(authRequired(monitor->url)) {
        monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO] = WEBSERVERMON_AUTHENTICATION_GEN0;
      }
      else {
        ;
        monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO] = WEBSERVERMON_AUTHENTICATION_WEBSERVER;
      }
      break;

    default:
      raise_error("webservermon_Authentication", webservermon_states_names[WEBSERVERMON_AUTHENTICATION_SCENARIO][monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO]], "request", "DEFAULT");
      break;
  }
}

void raise_webservermon_request(WebservermonMonitor* monitor, URL url) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, WEBSERVERMON_REQUEST_EVENT, p_head);
}


void webservermon_response(WebservermonMonitor* monitor, HTTPStatusCode code) {
  switch (monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO]) {
    case WEBSERVERMON_AUTHENTICATION_GEN0:
      if(monitor->code == 401) {
        monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO] = WEBSERVERMON_AUTHENTICATION_WEBSERVER;
      }
      else {
        ;
        monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO] = WEBSERVERMON_AUTHENTICATION_WEBSERVER;
      }
      break;

    default:
      raise_error("webservermon_Authentication", webservermon_states_names[WEBSERVERMON_AUTHENTICATION_SCENARIO][monitor->state[WEBSERVERMON_AUTHENTICATION_SCENARIO]], "response", "DEFAULT");
      break;
  }
}

void raise_webservermon_response(WebservermonMonitor* monitor, HTTPStatusCode code) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, WEBSERVERMON_RESPONSE_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_webservermon_monitor_maps() {
    if (pthread_mutex_init(&webservermon_monitor_maps_lock, NULL) != 0) {
        printf("\nWebservermon Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < WEBSERVERMON_MONITOR_IDENTITIES; i++) {
        webservermon_monitor_maps[i] = (WebservermonMonitorMap*)malloc(sizeof(WebservermonMonitorMap));
    }
    return 1;
}

int add_webservermon_monitor_to_map(WebservermonMonitor *monitor, int identity) {
    WebservermonMonitorMap* map = webservermon_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, WEBSERVERMON_MONITOR_MAP_SIZE);
    WebservermonMonitorRecord* record = (WebservermonMonitorRecord*)malloc(sizeof(WebservermonMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&webservermon_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&webservermon_monitor_maps_lock);
    return 1;
}

int put_webservermon_monitor(WebservermonMonitor *monitor) {
    return add_webservermon_monitor_to_map(monitor, WEBSERVERMON_ID);
}

WebservermonMonitorRecord* get_webservermon_monitors() {
    WebservermonMonitorRecord* results = NULL;
    WebservermonMonitorMap* map = webservermon_monitor_maps[0];
    for(int i = 0; i < WEBSERVERMON_MONITOR_MAP_SIZE; i++) {
        WebservermonMonitorRecord* current = map->list[i];
        while(current != NULL) {
            WebservermonMonitorRecord* record = (WebservermonMonitorRecord*)malloc(sizeof(WebservermonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

WebservermonMonitorRecord* get_webservermon_monitors_by_identity(int identity, int type, void *value) {
    WebservermonMonitorRecord* results = NULL;
    WebservermonMonitorMap* map = webservermon_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, WEBSERVERMON_MONITOR_MAP_SIZE);
    WebservermonMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            WebservermonMonitorRecord* record = (WebservermonMonitorRecord*)malloc(sizeof(WebservermonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

WebservermonMonitorRecord* filter_webservermon_monitors_by_identity(WebservermonMonitorRecord* before, int identity, void  *value) {
    WebservermonMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            WebservermonMonitorRecord* record = (WebservermonMonitorRecord*)malloc(sizeof(WebservermonMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}