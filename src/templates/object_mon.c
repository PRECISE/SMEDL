//Compile: gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "{{ base_file_name }}_mon.h"
{%- if helper %}{{ '\n' }}#include "{{ helper }}"{% endif %}

typedef enum { {{ identities_names|join(', ') }} } {{ obj|lower }}_identity;
const identity_type {{ obj|lower }}_identity_types[{{ obj|upper }}_MONITOR_IDENTITIES] = { {{ identities_types|join(', ') }} };

typedef enum { {{ scenario_names|join(', ') }} } {{ obj|lower }}_scenario;
{{ state_enums }}
typedef enum { {{ event_enums }} } {{ obj|lower }}_event;
typedef enum { {{ error_enums }} } {{ obj|lower }}_error;
{{ state_names }}
const char **{{ obj|lower }}_states_names[{{ state_names_array|length }}] = { {{ state_names_array|join(', ') }} };

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor( {{ obj|title }}Data *d ) {
    {{ obj|title }}Monitor* monitor = ({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
{% for id in identities %}    monitor->identities[{{ obj|upper }}_{{ id.name|upper }}] = init_monitor_identity({{ id.type|upper }}, {% if id.type|upper == "INT" %}&{% endif -%}d->{{ id.name }});
{% endfor -%}
{% for v in state_vars %}    monitor->{{ v.name }} = d->{{ v.name }};
{% endfor %}{{state_inits}}
    monitor->logFile = fopen("{{ obj|title }}Monitor.log", "w");
    put_{{ obj|lower }}_monitor(monitor);
    return monitor;
}

void free_monitor({{ obj|title }}Monitor* monitor) {
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

{% for e in event_code -%}
{{ e.event|join('\n') }}
{% if e.probe %}{{ '\n' }}{{ e.probe|join('\n') }}{{ '\n' }}{% endif %}
{{ e.raise|join('\n') }}
{% endfor -%}


/*
 * Monitor Utility Functions
 */

int init_{{ obj|lower }}_monitor_maps() {
    if (pthread_mutex_init(&{{ obj|lower }}_monitor_maps_lock, NULL) != 0) {
        printf("\n{{ obj|title }} Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < {{ obj|upper }}_MONITOR_IDENTITIES; i++) {
        {{ obj|lower }}_monitor_maps[i] = ({{ obj|title }}MonitorMap*)malloc(sizeof({{ obj|title }}MonitorMap));
    }
    return 1;
}

void free_{{ obj|lower }}_monitor_maps() {
    // TODO
}

int add_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity) {
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&{{ obj|lower }}_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&{{ obj|lower }}_monitor_maps_lock);
    return 1;
}

int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) {
    return {{ add_to_map_calls|join(' &&\n      ') }};
}

{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors() {
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[0];
    for(int i = 0; i < {{ obj|upper }}_MONITOR_MAP_SIZE; i++) {
        {{ obj|title }}MonitorRecord* current = map->list[i];
        while(current != NULL) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identity(int identity, int type, void *value) {
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord* before, int identity, void  *value) {
    {{ obj|title }}MonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
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
