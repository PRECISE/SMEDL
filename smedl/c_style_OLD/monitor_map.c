#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>
#include <string.h>
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
            free(p);
            free(t);
            break;
        case STRING:
            identity -> value = (char*)malloc((strlen((char*)value)+1)*sizeof(char));
            strcpy(identity -> value,(char*)value);
            free(i);
            free(p);
            free(t);
            break;
        case POINTER:
            *p = (uintptr_t)value;
            identity->value = p;
            free(i);
            free(t);
            break;
        case THREAD:
            *t = *(pthread_t*)value;
            identity->value = t;
            free(i);
            free(p);
            break;
        default:
            free(i);
            free(p);
            free(t);
            break;
    }
    return identity;
}

int compare_monitor_identity(void *value, MonitorIdentity *other) {
    int value_match = 0;
    switch (other->type) {
        case STRING:
            if(!strcmp((char*)value,(char*)(other -> value))){
                value_match = 1;
            }
            break;
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

int compare_identity(MonitorIdentity *v, MonitorIdentity *other) {
    int value_match = 0;
    switch (other->type) {
        case STRING:
            return strcmp((char*)(v->value), (char*)(other->value));
        case INT:
        case OPAQUE:
            return *(int*)(v->value) - *(int*)other->value;
        case POINTER:
            return *(uintptr_t*)(v->value) - *(uintptr_t*)(other->value);
        case THREAD:
            return *(pthread_t*)(v->value) - *(pthread_t*)(other->value);
        default:
            return -1;
    }
    return -1;
}

int compare_identity_2(void *value, MonitorIdentity *other) {
    int value_match = 0;
    switch (other->type) {
        case STRING:
            return strcmp((char*)(value), (char*)(other->value));
        case INT:
        case OPAQUE:
            return *(int*)(value) - *(int*)other->value;
        case POINTER:
            return *(uintptr_t*)(value) - *(uintptr_t*)(other->value);
        case THREAD:
            return *(pthread_t*)(value) - *(pthread_t*)(other->value);
        default:
            return -1;
    }
    return -1;
}

int hash_monitor_identity(identity_type type, void *value, int map_size) {
    int bucket;
    switch (type) {
        case STRING:
            if(value != NULL){
                // See djb2 from http://www.cse.yorku.ca/~oz/hash.html
                unsigned long int acc = 5381;
                for (int i = 0; i < strlen((char*) value); i++) {
                    //The next line is equiv to: acc = (acc * 31) ^ value[i]
                    acc = ((acc << 5) + acc) ^ ((char *)value)[i];
                }
                bucket = acc % map_size;
            }else{
                bucket = 0;
            }
            break;
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
        case STRING:
            strncpy(out,(char*)(id -> value),19);
            int index = strlen((char*)(id->value)) > 20 ? 20 : strlen((char*)(id->value));
            out[index] = '\0';
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
