#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include "monitor_map.h"

MonitorIdentity* init_monitor_identity(identity_type type, void *value) {
    MonitorIdentity* identity = (MonitorIdentity*)malloc(sizeof(MonitorIdentity));
    int *i = (int*)malloc(sizeof(int));
    uintptr_t *p = (uintptr_t*)malloc(sizeof(uintptr_t));
    pthread_t *t = (pthread_t*)malloc(sizeof(pthread_t));

    identity->type = type;

    switch (type) {
        case INT:
        case OPAQUE:
            *i = *(int*)value;
            identity->value = i;
            break;
        case POINTER:
            *p = (uintptr_t)value;
            identity->value = p;
            break;
        case THREAD:
            *t = *(pthread_t*)value;
            identity->value = t;
            break;
        default:
            break;
    }

    return identity;
}

int compare_monitor_identity(void *value, MonitorIdentity *other) {
    int value_match = 0;
    switch (other->type) {
        case INT:
        case OPAQUE:
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
            break;
        default:
            break;
    }
    return value_match;
}

int hash_monitor_identity(identity_type type, void *value, int map_size) {
    int bucket;
    switch (type) {
        case INT:
        case OPAQUE:
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

char* monitor_identity_str(MonitorIdentity *id) {
    char* out = malloc(20);
    out[0] = '\0';
    switch (id->type) {
        case INT:
        case OPAQUE:
            sprintf(out, "%d", *(int*)id->value);
            break;
        case POINTER:
            sprintf(out, "%02x", (int)*(uintptr_t*)id->value);
            break;
        case THREAD:
            sprintf(out, "%02x", (int)*(pthread_t*)id->value);
            break;
        default:
            out[0] = '\0';
            break;
    }
    return out;
}
