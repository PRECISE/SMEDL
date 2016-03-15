//Compile: gcc -o tab_example_mon -std=c99 actions.c monitor_map.c tab_example_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "tab_example_mon.h"

typedef enum { TABMON_ID, TABMON_TEST } tabmon_identity;
const identity_type tabmon_identity_types[TABMON_MONITOR_IDENTITIES] = { OPAQUE, OPAQUE };

typedef enum { TABMON_COOKIEINTEGRITY_SCENARIO, TABMON_PAGERENDERING_SCENARIO } tabmon_scenario;
typedef enum { TABMON_COOKIEINTEGRITY_TAB } tabmon_cookieintegrity_state;
typedef enum { TABMON_PAGERENDERING_TAB, TABMON_PAGERENDERING_GEN0 } tabmon_pagerendering_state;
typedef enum { TABMON_STORE_EVENT, TABMON_RENDER_EVENT, TABMON_DISPLAYURL_EVENT, TABMON_COOKIEINTEGRITYALARM_EVENT } tabmon_event;
typedef enum { TABMON_DEFAULT } tabmon_error;
const char *tabmon_cookieintegrity_states[1] = { "Tab" };
const char *tabmon_pagerendering_states[2] = { "Tab", "Gen0" };
const char **tabmon_states_names[2] = { tabmon_cookieintegrity_states, tabmon_pagerendering_states };

TabmonMonitor* init_tabmon_monitor( TabmonData *d ) {
    TabmonMonitor* monitor = (TabmonMonitor*)malloc(sizeof(TabmonMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[TABMON_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->identities[TABMON_TEST] = init_monitor_identity(OPAQUE, d->test);
    monitor->currentUrl = d->currentUrl;
    monitor->testUrl = d->testUrl;
    monitor->rengine = d->rengine;
    monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO] = TABMON_COOKIEINTEGRITY_TAB;
    monitor->state[TABMON_PAGERENDERING_SCENARIO] = TABMON_PAGERENDERING_TAB;
    put_tabmon_monitor(monitor);
    return monitor;
}


/*
 * Monitor Event Handlers
 */

void tabmon_store(TabmonMonitor* monitor, Tab this, Cookie cookie) {
  switch (monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]) {
    case TABMON_COOKIEINTEGRITY_TAB:
      if(isSubdomain(cookie.domain, monitor->currentUrl.getHost())) {
        monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO] = TABMON_COOKIEINTEGRITY_TAB;
      }
      else {
        ;
        monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO] = TABMON_COOKIEINTEGRITY_TAB;
      }
      break;

    default:
      raise_error("tabmon_CookieIntegrity", tabmon_states_names[TABMON_COOKIEINTEGRITY_SCENARIO][monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]], "store", "DEFAULT");
      break;
  }
  switch (monitor->state[TABMON_PAGERENDERING_SCENARIO]) {
    default:
      raise_error("tabmon_PageRendering", tabmon_states_names[TABMON_PAGERENDERING_SCENARIO][monitor->state[TABMON_PAGERENDERING_SCENARIO]], "store", "DEFAULT");
      break;
  }
}

void raise_tabmon_store(TabmonMonitor* monitor, Tab this, Cookie cookie) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, TABMON_STORE_EVENT, p_head);
}


void tabmon_render(TabmonMonitor* monitor, Renderer rengine, URL url) {
  switch (monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]) {
    default:
      raise_error("tabmon_CookieIntegrity", tabmon_states_names[TABMON_COOKIEINTEGRITY_SCENARIO][monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]], "render", "DEFAULT");
      break;
  }
  switch (monitor->state[TABMON_PAGERENDERING_SCENARIO]) {
    case TABMON_PAGERENDERING_GEN0:
        monitor->currentUrl = url;
      monitor->state[TABMON_PAGERENDERING_SCENARIO] = TABMON_PAGERENDERING_TAB;
      break;

    default:
      raise_error("tabmon_PageRendering", tabmon_states_names[TABMON_PAGERENDERING_SCENARIO][monitor->state[TABMON_PAGERENDERING_SCENARIO]], "render", "DEFAULT");
      break;
  }
}

void raise_tabmon_render(TabmonMonitor* monitor, Renderer rengine, URL url) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, TABMON_RENDER_EVENT, p_head);
}


void tabmon_displayUrl(TabmonMonitor* monitor, Tab this, URL url) {
  switch (monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]) {
    default:
      raise_error("tabmon_CookieIntegrity", tabmon_states_names[TABMON_COOKIEINTEGRITY_SCENARIO][monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]], "displayUrl", "DEFAULT");
      break;
  }
  switch (monitor->state[TABMON_PAGERENDERING_SCENARIO]) {
    case TABMON_PAGERENDERING_TAB:
      monitor->state[TABMON_PAGERENDERING_SCENARIO] = TABMON_PAGERENDERING_GEN0;
      break;

    default:
      raise_error("tabmon_PageRendering", tabmon_states_names[TABMON_PAGERENDERING_SCENARIO][monitor->state[TABMON_PAGERENDERING_SCENARIO]], "displayUrl", "DEFAULT");
      break;
  }
}

void raise_tabmon_displayUrl(TabmonMonitor* monitor, Tab this, URL url) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, TABMON_DISPLAYURL_EVENT, p_head);
}


void tabmon_cookieIntegrityAlarm(TabmonMonitor* monitor) {
  switch (monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]) {
    default:
      raise_error("tabmon_CookieIntegrity", tabmon_states_names[TABMON_COOKIEINTEGRITY_SCENARIO][monitor->state[TABMON_COOKIEINTEGRITY_SCENARIO]], "cookieIntegrityAlarm", "DEFAULT");
      break;
  }
  switch (monitor->state[TABMON_PAGERENDERING_SCENARIO]) {
    default:
      raise_error("tabmon_PageRendering", tabmon_states_names[TABMON_PAGERENDERING_SCENARIO][monitor->state[TABMON_PAGERENDERING_SCENARIO]], "cookieIntegrityAlarm", "DEFAULT");
      break;
  }
}

void raise_tabmon_cookieIntegrityAlarm(TabmonMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, TABMON_COOKIEINTEGRITYALARM_EVENT, p_head);
}


/*
 * Monitor Utility Functions
 */

int init_tabmon_monitor_maps() {
    if (pthread_mutex_init(&tabmon_monitor_maps_lock, NULL) != 0) {
        printf("\nTabmon Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < TABMON_MONITOR_IDENTITIES; i++) {
        tabmon_monitor_maps[i] = (TabmonMonitorMap*)malloc(sizeof(TabmonMonitorMap));
    }
    return 1;
}

int add_tabmon_monitor_to_map(TabmonMonitor *monitor, int identity) {
    TabmonMonitorMap* map = tabmon_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, TABMON_MONITOR_MAP_SIZE);
    TabmonMonitorRecord* record = (TabmonMonitorRecord*)malloc(sizeof(TabmonMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&tabmon_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&tabmon_monitor_maps_lock);
    return 1;
}

int put_tabmon_monitor(TabmonMonitor *monitor) {
    return add_tabmon_monitor_to_map(monitor, TABMON_ID) &&
      add_tabmon_monitor_to_map(monitor, TABMON_TEST);
}

TabmonMonitorRecord* get_tabmon_monitors() {
    TabmonMonitorRecord* results = NULL;
    TabmonMonitorMap* map = tabmon_monitor_maps[0];
    for(int i = 0; i < TABMON_MONITOR_MAP_SIZE; i++) {
        TabmonMonitorRecord* current = map->list[i];
        while(current != NULL) {
            TabmonMonitorRecord* record = (TabmonMonitorRecord*)malloc(sizeof(TabmonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

TabmonMonitorRecord* get_tabmon_monitors_by_identity(int identity, int type, void *value) {
    TabmonMonitorRecord* results = NULL;
    TabmonMonitorMap* map = tabmon_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, TABMON_MONITOR_MAP_SIZE);
    TabmonMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            TabmonMonitorRecord* record = (TabmonMonitorRecord*)malloc(sizeof(TabmonMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

TabmonMonitorRecord* filter_tabmon_monitors_by_identity(TabmonMonitorRecord* before, int identity, void  *value) {
    TabmonMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            TabmonMonitorRecord* record = (TabmonMonitorRecord*)malloc(sizeof(TabmonMonitorRecord));
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