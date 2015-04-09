#include <stdlib.h>
#include <stdio.h>
#include "actions.h"

int push_param(param **head, int *i, char *c, double *d) {
    param *new = (param*)malloc(sizeof(param));
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
    if(head != NULL && *head != NULL) {
        param *old = *head;
        *head = (*head)->next;
        free(old);    
    }
}

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




