#include <stdlib.h>
#include <stdio.h>
#include "actions.h"
#include "mon_utils.h"
#include "monitor_map.h"
{% if genjson -%}
#include "cJSON.h"
{% endif -%}


int push_param(param **head, int *i, char *c, double *d, const void **v{%if genjson %}, cJSON * pro{% endif %}) {
#ifdef DEBUG
    param *new = calloc(1, sizeof(param));
#else //DEBUG
    param *new = malloc(sizeof(param));
#endif //DEBUG
    if(new == NULL) {
        free(new);
        return 0;
    }
    if(i != NULL) {
        new->i = *i;
    }
    if(c != NULL) {
        new->c = *c;
    }
    if(d != NULL) {
        new->d = *d;
    }
    if(v != NULL) {
        new->v = *v;
    }
    {% if genjson -%}
    if (pro != NULL){
        new->provenance = pro;
    }else{
        new->provenance = NULL;
    }
    {% endif -%}
    new->next = NULL;
    if(*head == NULL) {
        *head = new;
        return 1;
    }
    param *current = *head;
    while(current->next != NULL) {
        current = current->next;
    }
    current->next = new;
    return 1;
}

void pop_param(param **head) {
    while(head != NULL && *head != NULL) {
        param *old = *head;
        *head = (*head)->next;
        free(old);
    }
}

#ifdef DEBUG
void print_param(param *head, char *types) {
    printf("Params:");
    for (int i = 0; types[i] != '\0'; i++) {
        printf(" ");
        switch (types[i]) {
            case 'i':
                printf("int:%d", head->i);
                break;
            case 'c':
                printf("char:%c", head->c);
                break;
            case 'd':
                printf("double:%lf", head->d);
                break;
            case 'v':
                printf("string:%s", head->v);
                break;
            {% if genjson -%}
            default:
                printf("pro:<data>");
            {% endif -%}
        }
        head = head->next;
    }
    printf("\n");
}
#endif //DEBUG

int push_action(action **head, int id, param *params) {
    action *new = (action*)malloc(sizeof(action));
    if(new == NULL) {
        free(new);
        return 0;
    }
    new->id = id;
    new->params = params;
    new->next = NULL;
    if(*head == NULL) {
        *head = new;
        return 1;
    }
    action *current = *head;
    while((current)->next != NULL) {
        current = current->next;
    }
    current->next = new;
    return 1;
}

void pop_action(action **head) {
    if(head != NULL && *head != NULL) {
        action *old = *head;
        *head = (*head)->next;
        free(old);
    }
}

int push_global_action(global_action **head, int monitor_type, MonitorIdentity **identities, int id, param *params) {
    global_action *new = (global_action*)malloc(sizeof(global_action));
    if(new == NULL) {
        free(new);
        return 0;
    }
    new->monitor_type = monitor_type;
    new->identities = identities;
    new->id = id;
    new->params = params;
    new->next = NULL;
    if(*head == NULL) {
        *head = new;
        return 1;
    }
    global_action *current = *head;
    while((current)->next != NULL) {
        current = current->next;
    }
    current->next = new;
    return 1;
}

void pop_global_action(global_action **head) {
    if(head != NULL && *head != NULL) {
        global_action *old = *head;
        *head = (*head)->next;
        free(old);
    }
}
