//Compile: gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "cJSON.h"
#include "mon_utils.h"
#include "{{ base_file_name }}_mon.h"
#include "{{ sync_set_name }}_global_wrapper.h"

#define ARRAYSIZE(arr) (sizeof(arr) / sizeof(arr[0]))


{%- if helper %}{{ '\n' }}#include "{{ helper }}"{% endif %}

{{ state_names }}
const identity_type {{ obj|lower }}_identity_types[{{ obj|upper }}_MONITOR_IDENTITIES] = { {{ identities_types|join(', ') }} };
const char **{{ obj|lower }}_states_names[{{ state_names_array|length }}] = { {{ state_names_array|join(', ') }} };
int {{ obj|lower }}_executed_scenarios[{{num_scenarios}}]={ {{ zeros }} };
{{ obj|title }}MonitorRecord * {{ obj|lower }}_monitorPoolHead = NULL;

//({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor( {{ obj|title }}Data *d ) {
    {{ obj|title }}Monitor* monitor = {{ obj|lower }}_getMonitorObject();
    pthread_mutex_init(&monitor->monitor_lock, NULL);
{% for id in identities %}    monitor->identities[{{ obj|upper }}_{{ id.name|upper }}] = init_monitor_identity({{ id.type|upper }}, {% if id.type|upper == "INT" %}&{% endif -%}d->{{ id.name }});

{% endfor -%}
{% for v in state_vars %}    monitor->{{ v.name }} = d->{{ v.name }};
{% endfor %}{{state_inits}}
    monitor->action_queue = NULL;
    monitor->recycleFlag = 0;
    
    put_{{ obj|lower }}_monitor(monitor);
    return monitor;
}

void free_{{ obj|lower }}_monitor({{ obj|title }}Monitor* monitor) {
    free(monitor);
}

//called at the end of each event handling function
void executeEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor){
    if(monitor->action_queue != NULL){
        executePendingEvents_{{ obj|lower }}(monitor);
    } else {
        if (monitor -> recycleFlag == 1){
            remove_{{obj|lower}}_monitor(monitor);
        }
        memset({{ obj|lower }}_executed_scenarios, 0, sizeof({{ obj|lower }}_executed_scenarios));
    }

}

void executePendingEvents_{{ obj|lower }}({{obj|title}}Monitor* monitor){
    action** head = &monitor->action_queue;
    {{var_declaration}} cJSON* pro;
    while(*head!=NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type){
            {% for e in pending_event_case -%}
            case {{ e.event_enum|join('\n') }}
            {{e.callstring}}
                break;
            {% endfor -%}
        }
        //pop_action(head);
    }
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

//first try to get a monitor object from the pool, if there is none, create one
{{ obj|title }}Monitor* {{ obj|lower }}_getMonitorObject(){
    if ({{ obj|lower }}_monitorPoolHead == NULL){
        printf("newly created monitor\n");
        {{ obj|title }}Monitor* monitor = ({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));
        return monitor;
    }else{
        {{ obj|title }}MonitorRecord *record = {{ obj|lower }}_monitorPoolHead;
        {{ obj|lower }}_monitorPoolHead = {{ obj|lower }}_monitorPoolHead -> next;
        printf("picked from pool\n");
        return record->monitor;
    }
}

int {{ obj|lower }}_addMonitorObjectToPool({{ obj|title }}MonitorRecord* record){
    if ({{ obj|lower }}_monitorPoolHead == NULL){
        printf("monitor object removed\n");
        {{ obj|lower }}_monitorPoolHead = record;
        return 0;
    }
    {{ obj|title }}MonitorRecord* temp = {{ obj|lower }}_monitorPoolHead;
    {{ obj|title }}MonitorRecord* pre_temp = NULL;
    while(temp != NULL && temp -> monitor != NULL){
        if(temp -> monitor == record -> monitor){
            printf("already removed\n");
            return 1;
        }
        pre_temp = temp;
        temp = temp -> next;
    }
    pre_temp -> next = record;
    printf("monitor object removed\n");
    return 0;
}


int remove_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity) {
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
                                       monitor->identities[identity]->value, {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* current = map->list[bucket];
    {{ obj|title }}MonitorRecord* current_pre = NULL;
    while(current != NULL) {
        if (monitor == current->monitor){
            pthread_mutex_lock(&{{ obj|lower }}_monitor_maps_lock);
            if (current == map->list[bucket]){
                map->list[bucket] =  map->list[bucket] -> next;
            }else{
                current_pre -> next = current -> next;
            }
            pthread_mutex_unlock(&{{ obj|lower }}_monitor_maps_lock);
            if ({{ obj|lower }}_addMonitorObjectToPool(current)){
                printf("no need to add duplicate objects");
                free(current);
            }
            return 0;
        }
        current_pre = current;
        current = current->next;
    }
    return 1;
}

void remove_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) {
    {% for v in identities_names %}    remove_{{ obj|lower }}_monitor_to_map(monitor, {{v}});
    {% endfor %}
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

{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identities(int identity[], int type, void *value[], int size) {
    if(identity == NULL || value == NULL)
        return NULL;
    //if(ARRAYSIZE(identity) != ARRAYSIZE(value))
        //return NULL;
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity[0]];
    int bucket = hash_monitor_identity(type, value[0], {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value[0], current->monitor->identities[identity[0]])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    for(int i = 1; i<size;i++){
        results = filter_{{ obj|lower }}_monitors_by_identity(results, identity[i], value[i]);
    }
    return results;
}

char* monitor_identities_str_{{ obj|lower }}(MonitorIdentity** identities) {
    char* out = malloc(20*{{ obj|upper }}_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < {{ obj|upper }}_MONITOR_IDENTITIES; i++) {
        char* monid_str = monitor_identity_str(identities[i]);
        if (i == 0) {
            strcat(out, monid_str);
        }
        else {
            strcat(out, ", ");
            strcat(out, monid_str);
        }
        free(monid_str);
    }
    return out;
}
