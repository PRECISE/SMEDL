#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "mon_utils.h"
{% if genjson -%}
#include "cJSON.h"
{% endif -%}
#include "{{ base_file_name }}_mon.h"
#include "{{ base_file_name }}_monitor_wrapper.h"
#include "{{ sync_set_name }}_global_wrapper.h"

// This function handles imported events.
// The first 4 parameters align with get_{{ obj|lower }}_monitors_by_identities. If there are no identities to match,
// they should be NULL, 0, NULL, 0 (although it doesn't really matter).
// event_id is from the {{ obj|lower }}_event enum
// params are the parameters of the event

{%- for m in imported_event_case %}
    {%- for e in m.import_event %}
    void import_{{m.import_obj}}_{{e}}_event(int identity[], int type, void *values[], int size, param *params){
        {{ obj|title }}MonitorRecord* record;
        {{m.callstring}}
    }
    {%- endfor %}
{%- endfor %}

// Handle events to be exported to RabbitMQ from the global wrapper.
void export_async_event_{{ obj|lower }}(MonitorIdentity** identities, int event_id, param *params) {
    param *p_head = params;

    switch (event_id) {
        {% for e in exported_event_case -%}
        case {{ e.event_enum|join('\n') }}
            {{e.callstring}}
            break;
        {% endfor -%}
    }
}

// Monitor/Monitor Wrapper Changes start from here 

int init_{{ obj|lower }}_monitor_maps() {
    if (pthread_mutex_init(&{{ obj|lower }}_monitor_maps_lock, NULL) != 0) {
        printf("\n{{ obj|title }} Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < {{ obj|upper }}_MONITOR_IDENTITIES; i++) {
        {{ obj|lower }}_monitor_maps[i] = calloc(1, sizeof({{ obj|title }}MonitorMap));
    }
    return 1;
}

void free_{{ obj|lower }}_monitor_maps() {
    // TODO
}

int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) {
    return {{ add_to_map_calls|join(' &&\n      ') }};
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
    //pthread_mutex_lock(&{{ obj|lower }}_monitor_maps_lock);
    record->next = NULL;
    record->left = NULL;
    record->right = NULL;
    if (map->list[bucket] == NULL) {
        map->list[bucket] = record;
    } else {
        insert_{{ obj|lower }}_record(map->list[bucket], record, identity, bucket);
    }
    //pthread_mutex_unlock(&{{ obj|lower }}_monitor_maps_lock);
    return 1;
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

void insert_{{ obj|lower }}_record({{ obj|title }}MonitorRecord *root, {{ obj|title }}MonitorRecord *e, int identity, int bucket) {
    if (root == NULL) {
        return;
    }

    int r = compare_identity(root->monitor->identities[identity], e->monitor->identities[identity]);
    if (r < 0) {
        if (root->left != NULL) {
            insert_{{ obj|lower }}_record(root->left, e, identity, bucket);
        } else {
            root->left = e;
        }
    } else if (r > 0) {
        if (root->right != NULL) {
            insert_{{ obj|lower }}_record(root->right, e, identity, bucket);
        } else {
            root->right = e;
        }
    } else {
        {{ obj|title }}MonitorRecord *p = root;
        while (p != NULL && p->next != NULL) {
            p = p->next;
        }
        p->next = e;
        e->next = NULL;
    }
}


{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors() {
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorRecord* cur_results = NULL;
    {{ obj|title }}MonitorRecord* temp_cur = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[0];

    int i;
    for(i = 0; i < {{ obj|upper }}_MONITOR_MAP_SIZE; i++) {
        if (map->list[i] != NULL) {
            cur_results = traverseAndGet_{{ obj|lower }}(map->list[i], i);
            break;
        }
    }
    i++;

    temp_cur = cur_results;
    while (temp_cur != NULL && temp_cur->next != NULL) {
        temp_cur = temp_cur->next;
    }

    for (; i < {{ obj|upper }}_MONITOR_MAP_SIZE; i++) {
        {{ obj|title }}MonitorRecord *current = map->list[i];
        results = traverseAndGet_{{ obj|lower }}(current, i);
        temp_cur->next = results;
        while (temp_cur->next != NULL) {
            temp_cur = temp_cur->next;
        }
    }
    return cur_results;
}

{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identities(int identity[], int type, void *value[], int size) {
    if(identity == NULL || value == NULL)
        return NULL;
    //if(ARRAYSIZE(identity) != ARRAYSIZE(value))
        //return NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity[0]];
    int bucket = hash_monitor_identity(type, value[0], {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* current = map->list[bucket];
    {{ obj|title }}MonitorRecord* results = NULL;
    /*
    while(current != NULL) {
        if(compare_monitor_identity(value[0], current->monitor->identities[identity[0]])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }*/
    results = find_{{ obj|lower }}_record(current, value[0], identity[0]);

    for(int i = 1; i<size;i++){
        results = filter_{{ obj|lower }}_monitors_by_identity(results, identity[i], value[i]);
    }
    return results;
}


{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord* before, int identity, void  *value) {
    {{ obj|title }}MonitorRecord* tmp;
    {{ obj|title }}MonitorRecord* current = before;
    {{ obj|title }}MonitorRecord* prev = NULL;

    while(current != NULL) {
        if(!compare_monitor_identity(value, before->monitor->identities[identity])) {
            if (current == before) {
                before = before->next;
            } else {
                prev->next = current->next;
            }

            tmp = current;
            current = current->next;
            free(tmp);
        } else {
            prev = current;
            current = current->next;
        }
    }

    return before;
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


{{ obj|title }}MonitorRecord* find_{{ obj|lower }}_record({{ obj|title }}MonitorRecord *root, void *value, int identity) {
    if (root == NULL) {
        return NULL;
    }

    int r = compare_identity_2(value, root->monitor->identities[identity]);

    if (r > 0) {
        if (root->left != NULL) {
            find_{{ obj|lower }}_record(root->left, value, identity);
        } else {
            return NULL;
        }
    } else if (r < 0) {
        if (root->right != NULL) {
            find_{{ obj|lower }}_record(root->right, value, identity);
        } else {
            return NULL;
        }
    } else {
        {{ obj|title }}MonitorRecord *p = root;
        {{ obj|title }}MonitorRecord *results = NULL;
        while (p != NULL) {
            {{ obj|title }}MonitorRecord *record = malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = p->monitor;
            record->next = results;
            results = record;
            p = p->next;
        }
        return results;
    }
}


{{ obj|title}}MonitorRecord* traverseAndGet_{{ obj|lower }}({{ obj|title}}MonitorRecord *current, int bucket) {
    {{ obj|title}}MonitorRecord *l = NULL;
    {{ obj|title}}MonitorRecord *r = NULL;
    {{ obj|title}}MonitorRecord *results = NULL;
    {{ obj|title}}MonitorRecord *tmp = current;
    if (current == NULL) {
        return NULL;
    }

    while (current != NULL) {
        {{ obj|title}}MonitorRecord *record = malloc(sizeof({{ obj|title}}MonitorRecord));
        record->monitor = current->monitor;
        record->next = results;
        results = record;
        current = current->next;
    }

    if (tmp->left != NULL) {
        l = traverseAndGet_{{ obj|lower }}(tmp->left, bucket);
    }
    if (tmp->right != NULL) {
        r = traverseAndGet_{{ obj|lower }}(tmp->right, bucket);
    }

    {{ obj|title}}MonitorRecord *p = results;
    while (p != NULL && p->next != NULL) {
        p = p->next;
    }
    if (l != NULL) {
        p->next = l;
        while (l != NULL && l->next != NULL) {
            l = l->next;
        }
        l->next = r;
    } else {
        p->next = r;
    }

    return results;
}