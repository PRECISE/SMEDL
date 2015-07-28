#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include "monitor_map.h"

MonitorIdentity* init_MonitorIdentity(identity_type type, void *value) {
    MonitorIdentity* identity = (MonitorIdentity*)malloc(sizeof(MonitorIdentity));
    identity->type = type;
    switch (type) {
        case INT:;
            int *i = (int*)malloc(sizeof(int));
            *i = *(int*)value;
            identity->value = i;
            break;
        case POINTER:;
            uintptr_t *p = (uintptr_t*)malloc(sizeof(uintptr_t));
            *p = (uintptr_t)value;
            identity->value = p;
            printf("Pointer stored: %zu\n", *(uintptr_t*)identity->value);
            break;
        case THREAD: ;
            pthread_t *t = (pthread_t*)malloc(sizeof(pthread_t));
            *t = *(pthread_t*)value;
            identity->value = t;
        default:
            break;
    }
    return identity;
}

int compare_MonitorIdentity(void *value, MonitorIdentity *other) {
    int value_match = 0;
    printf("Type being checked: %d\n", other->type);
    switch (other->type) {
        case INT:
            printf("Comparing ints: %d %d\n", *(int*)value, *(int*)other->value);
            if(*(int*)value == *(int*)other->value) {
                value_match = 1;
            }
            break;
        case POINTER:
            printf("Comparing pointers: %zu %zu\n", *(uintptr_t*)value, *(uintptr_t*)other->value);
            if(*(uintptr_t*)value == *(uintptr_t*)other->value) {
                value_match = 1;
            }
            break;
        case THREAD:
            printf("Comparing threads: %d, %d\n", ((int)*(pthread_t*)value), ((int)*(pthread_t*)other->value));
            if(*(pthread_t*)value == *(pthread_t*)other->value) {
                value_match = 1;
            }           
        default:
            break;
    }
    return value_match;
}

int hash_MonitorIdentity(identity_type type, void *value) {
    int bucket;
    switch (type) {
        case INT: ;
            bucket = *(int*)value % EXPLORER_MONITOR_MAP_SIZE;
            printf("Type and value being hashed: %d, %d\n", type, *(int*)value);
            break;
        case POINTER:
            bucket = (int)(*(uintptr_t*)value) % EXPLORER_MONITOR_MAP_SIZE;
            printf("Type and value being hashed: %d, %zu\n", type, *(uintptr_t*)value);
            printf("Bucket for pointer: %d\n", bucket);
            break;
        case THREAD:
            printf("Type and value being hashed: %d, %d\n", type, ((int)*(pthread_t*)value));
            bucket = (int)(*(pthread_t*)value) % EXPLORER_MONITOR_MAP_SIZE;
            printf("Ok...\n");
        default:
            break;
    }
    return bucket; 
}

typedef enum { EXPLORER_ID, EXPLORER_DATA, EXPLORER_THREAD_ID } explorer_identity_tag;
const identity_type explorer_identity_types[2] = { POINTER, INT};

_Explorer* init_Explorer(int id, void *data, pthread_t *thread_id, int x, int y) {
    _Explorer* monitor = (_Explorer*)malloc(sizeof(_Explorer));
    monitor->identities[EXPLORER_ID] = init_MonitorIdentity(INT, &id);
    monitor->identities[EXPLORER_DATA] = init_MonitorIdentity(POINTER, data);
    monitor->identities[EXPLORER_THREAD_ID] = init_MonitorIdentity(THREAD, thread_id);
    monitor->x = x;
    monitor->y = y;
    put_explorer_monitor(monitor);
    return monitor;
}

void init_explorer_maps() {
    for(int i = 0; i < EXPLORER_IDENTITIES; i++) {
        explorer_monitor_maps[i] = (ExplorerMonitorMap*)malloc(sizeof(ExplorerMonitorMap));
    }
}


int add_explorer_to_map(_Explorer *monitor, int identity) {
    ExplorerMonitorMap* map = explorer_monitor_maps[identity];
    int bucket = hash_MonitorIdentity(monitor->identities[identity]->type, monitor->identities[identity]->value);
    ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    record->next = map->list[bucket];
    map->list[bucket] = record;
    printf("Added %d\n", identity);
    return 1; 
}

int put_explorer_monitor(_Explorer *monitor) {
    return add_explorer_to_map(monitor, EXPLORER_ID) && 
        add_explorer_to_map(monitor, EXPLORER_DATA) &&
        add_explorer_to_map(monitor, EXPLORER_THREAD_ID);
}

ExplorerMonitorRecord* get_explorer_by_identity(int identity, int type, void *value) {
    ExplorerMonitorRecord* results = NULL;
    ExplorerMonitorMap* map = explorer_monitor_maps[identity];
    int bucket = hash_MonitorIdentity(type, value);
    ExplorerMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        printf("Type being looked at: %d\n", current->monitor->identities[identity]->type);
        if(compare_MonitorIdentity(value, current->monitor->identities[identity])) {
            printf("Match %d %zu\n", *((int*)current->monitor->identities[0]->value), *(uintptr_t*)current->monitor->identities[0]->value);
            ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;          
        }
        current = current->next;
    }
    return results;
}

ExplorerMonitorRecord* filter_explorer_by_identity(ExplorerMonitorRecord* before, int identity, void  *value) {
    ExplorerMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_MonitorIdentity(value, before->monitor->identities[identity])) {
            ExplorerMonitorRecord* record = (ExplorerMonitorRecord*)malloc(sizeof(ExplorerMonitorRecord)); 
            record->monitor = before->monitor;
            record->next = results;
            results = record;               
        }
        before = before->next;
    }
    return results;
}

void print_results(ExplorerMonitorRecord *results) {
    if(results == NULL) {
        printf("No results\n");
        return;
    }
    while(results != NULL) {
        printf("%d, %d\n", results->monitor->x, results->monitor->y);
        results = results->next;
    }
}

void up_x_event(int x, int match_id, int** match_data) {
    ExplorerMonitorRecord *results1 = get_explorer_by_identity(EXPLORER_ID, INT, &match_id);
    ExplorerMonitorRecord *current = results1;
    while(current != NULL) {
        current->monitor->x = x;
        current = current->next;
    } 
    printf("Results1:\n"); 
    print_results(results1); 

    ExplorerMonitorRecord *results2 = filter_explorer_by_identity(results1, EXPLORER_DATA, match_data);
    printf("Results2:\n"); 
    print_results(results2); 
}

int main() {
    init_explorer_maps();
    int one = 1;
    int two = 2;
    int *one_ptr = &one;
    int *two_ptr = &two;
    pthread_t thread = pthread_self();
    printf("Making monitors\n\n");
    _Explorer *oneone = init_Explorer(1, &one, &thread, 1, 1);
    _Explorer *onetwo = init_Explorer(1, &two, &thread, 1, 2);
    _Explorer *twoone = init_Explorer(2, &one, &thread, 2, 3);
    _Explorer *twotwo = init_Explorer(2, &two, &thread, 2, 4);

    pthread_t thread_copy = pthread_self();

    printf("\nFinding all monitors in this thread\n\n");
    ExplorerMonitorRecord *all = get_explorer_by_identity(EXPLORER_THREAD_ID, THREAD, &thread_copy);
    print_results(all);

    printf("\nFinding monitors by first data\n\n");
    ExplorerMonitorRecord *results = get_explorer_by_identity(EXPLORER_DATA, POINTER, &one_ptr);
    print_results(results);

    printf("\nUp event (First two explorers should be 5,1 5,2\n\n");    
    up_x_event(5, 1, &two_ptr);
    printf("\n");
    print_results(results);
}
  


