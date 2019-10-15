//Compile: gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
{% if genjson -%}
#include "cJSON.h"
{% endif -%}
#include "mon_utils.h"
#include "{{ base_file_name }}_mon.h"
#include "{{ sync_set_name }}_global_wrapper.h"
#include "{{ base_file_name }}_monitor_wrapper.h"

#define ARRAYSIZE(arr) (sizeof(arr) / sizeof(arr[0]))


{%- if helper %}{{ '\n' }}#include "{{ helper }}"{% endif %}

{{ state_names }}
const identity_type {{ obj|lower }}_identity_types[{{ obj|upper }}_MONITOR_IDENTITIES] = { {{ identities_types|join(', ') }} };
const char **{{ obj|lower }}_states_names[{{ state_names_array|length }}] = { {{ state_names_array|join(', ') }} };
int {{ obj|lower }}_executed_scenarios[{{num_scenarios}}]={ {{ zeros }} };
{{ obj|title }}MonitorPoolRecord * {{ obj|lower }}_monitorPoolHead = NULL;

//({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor( {{ obj|title }}Data *d ) {
    {{ obj|title }}Monitor* monitor = {{ obj|lower }}_getMonitorObject();
    pthread_mutex_init(&monitor->monitor_lock, NULL);
{% for id in identities %}    monitor->identities = d->identities;
{% endfor -%}
{% for v in state_vars %}    monitor->{{ v.name }} = d->{{ v.name }};
{% endfor %}{{state_inits}}
    monitor->action_queue = NULL;
    monitor->recycleFlag = 0;
    
    //put_{{ obj|lower }}_monitor(monitor);
    return monitor;
}

{{ obj|title }}Monitor* init_default_{{ obj|lower }}_monitor(MonitorIdentity **identities) {
    {{ obj|title }}Data *d = malloc(sizeof({{ obj|title }}Data));
    d->identities = identities;
    {{ mon_init_str }}

    return init_{{ obj|lower }}_monitor(d);
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
    {{var_declaration}}
    {% if genjson -%}
    cJSON* pro;
    {% endif -%}
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

//first try to get a monitor object from the pool, if there is none, create one
{{ obj|title }}Monitor* {{ obj|lower }}_getMonitorObject(){
    if ({{ obj|lower }}_monitorPoolHead == NULL){
#ifdef DEBUG
        printf("newly created monitor\n");
#endif //DEBUG
        {{ obj|title }}Monitor* monitor = ({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));
        return monitor;
    }else{
        {{ obj|title }}MonitorPoolRecord *record = {{ obj|lower }}_monitorPoolHead;
        {{ obj|lower }}_monitorPoolHead = {{ obj|lower }}_monitorPoolHead -> next;
#ifdef DEBUG
        printf("picked from pool\n");
#endif //DEBUG
        return record->monitor;
    }
}

int {{ obj|lower }}_addMonitorObjectToPool({{ obj|title }}MonitorPoolRecord* record){
    if ({{ obj|lower }}_monitorPoolHead == NULL){
        printf("monitor object removed\n");
        {{ obj|lower }}_monitorPoolHead = record;
        return 0;
    }
    {{ obj|title }}MonitorPoolRecord* temp = {{ obj|lower }}_monitorPoolHead;
    {{ obj|title }}MonitorPoolRecord* pre_temp = NULL;
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
