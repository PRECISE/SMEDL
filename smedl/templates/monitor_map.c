#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include "monitor_map.h"

MonitorIdentity* init_monitor_identity(identity_type type, void *value) {
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
            break;
        case THREAD:;
            pthread_t *t = (pthread_t*)malloc(sizeof(pthread_t));
            *t = *(pthread_t*)value;
            identity->value = t;
        default:
            break;
    }
    return identity;
}

int compare_monitor_identity(void *value, MonitorIdentity *other) {
    int value_match = 0;
    switch (other->type) {
        case INT:
            if(*(int*)value == *(int*)other->value) {
                value_match = 1;
            }
            break;
        case POINTER:
            if(*(uintptr_t*)value == *(uintptr_t*)other->value) {
                value_match = 1;
            }
            break;
        case THREAD:
            if(*(pthread_t*)value == *(pthread_t*)other->value) {
                value_match = 1;
            }
        default:
            break;
    }
    return value_match;
}

int hash_monitor_identity(identity_type type, void *value, int map_size) {
    int bucket;
    switch (type) {
        case INT:
            bucket = *(int*)value % map_size;
            break;
        case POINTER:
            bucket = (int)(*(uintptr_t*)value) % map_size;
            break;
        case THREAD:
            bucket = (int)(*(pthread_t*)value) % map_size;
            break;
        default:
            break;
    }
    return bucket;
}
