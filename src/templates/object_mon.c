//Compile: gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

#include <stdio.h>
#include <stdlib.h>
#include "{{base_file_name}}_mon.h"
{%- if helper %}{{'\n'}}#include "{{helper}}"{% endif %}

typedef enum { {{identities_names|join(', ')}}} {{obj|lower}}_identity;
const identity_type {{obj|lower}}_identity_types[{{obj|upper}}_MONITOR_IDENTITIES] = { {{ identities_types|join(', ') }} };

typedef enum { {{ scenario_names|join(', ') }} } {{obj|lower}}_scenario;
{{state_enums}}
typedef enum { {{event_enums}} } {{obj|lower}}_event;
typedef enum { {{error_enums}} } {{obj|lower}}_error;
{{state_names}}
const char **{{obj|lower}}_states_names[{{state_names_array|length}}] = { {{state_names_array|join(', ')}} };

{{obj|title}}Monitor* init_{{obj|lower}}_monitor( {{obj|title}}Data *d ) {
    {{obj|title}}Monitor* monitor = ({{obj|title}}Monitor*)malloc(sizeof({{obj|title}}Monitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
{% for id in identities %}    monitor->identities[{{obj|upper}}_{{id.name|upper}}] = init_monitor_identity({{id.type|upper}}, {% if id.type|upper == "INT" %}&{% endif -%}d->{{id.name}});
{% endfor -%}
{% for v in state_vars %}    monitor->{{v.name|lower}} = d->{{v.name|lower}};
{% endfor %}{{state_inits}}  
    put_{{obj|lower}}_monitor(monitor);
    return monitor;
}

int init_{{obj|lower}}_monitor_maps() {
    if (pthread_mutex_init(&{{obj|lower}}_monitor_maps_lock, NULL) != 0) {
        printf("\n{{obj|title}} Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < {{obj|upper}}_MONITOR_IDENTITIES; i++) {
        {{obj|lower}}_monitor_maps[i] = ({{obj|title}}MonitorMap*)malloc(sizeof({{obj|title}}MonitorMap));
    }
    return 1;
}

int add_{{obj|lower}}_monitor_to_map({{obj|title}}Monitor *monitor, int identity) {
    {{obj|title}}MonitorMap* map = {{obj|lower}}_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type, 
        monitor->identities[identity]->value, {{obj|upper}}_MONITOR_MAP_SIZE);
    {{obj|title}}MonitorRecord* record = ({{obj|title}}MonitorRecord*)malloc(sizeof({{obj|title}}MonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&{{obj|lower}}_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&{{obj|lower}}_monitor_maps_lock);
    return 1; 
}

int put_{{obj|lower}}_monitor({{obj|title}}Monitor *monitor) {
    return {{add_to_map_calls|join(' &&\n      ')}};
}

{{obj|title}}MonitorRecord* get_{{obj|lower}}_monitors() {
    {{obj|title}}MonitorRecord* results = NULL;
    {{obj|title}}MonitorMap* map = {{obj|lower}}_monitor_maps[0];
    for(int i = 0; i < {{obj|upper}}_MONITOR_MAP_SIZE; i++) {
        {{obj|title}}MonitorRecord* current = map->list[i];
        while(current != NULL) {
            {{obj|title}}MonitorRecord* record = ({{obj|title}}MonitorRecord*)malloc(sizeof({{obj|title}}MonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;  
            current = current->next;        
        }   
    }
    return results; 
}

{{obj|title}}MonitorRecord* get_{{obj|lower}}_monitors_by_identity(int identity, int type, void *value) {
    {{obj|title}}MonitorRecord* results = NULL;
    {{obj|title}}MonitorMap* map = {{obj|lower}}_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, {{obj|upper}}_MONITOR_MAP_SIZE);
    {{obj|title}}MonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            {{obj|title}}MonitorRecord* record = ({{obj|title}}MonitorRecord*)malloc(sizeof({{obj|title}}MonitorRecord)); 
            record->monitor = current->monitor;
            record->next = results;
            results = record;       
        }
        current = current->next;
    }
    return results;
}

{{obj|title}}MonitorRecord* filter_{{obj|lower}}_monitors_by_identity({{obj|title}}MonitorRecord* before, int identity, void  *value) {
    {{obj|title}}MonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            {{obj|title}}MonitorRecord* record = ({{obj|title}}MonitorRecord*)malloc(sizeof({{obj|title}}MonitorRecord)); 
            record->monitor = before->monitor;
            record->next = results;
            results = record;               
        }
        before = before->next;
    }
    return results;
}

{% for e in event_code -%}
{{e.event|join('\n')}}

{{e.raise|join('\n')}}
{% endfor -%}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
}

int main() { //To prevent warnings for test compile (they even happen with -c)
  return 0;
}

// TODO add back original smedlgen stuff:

// void drive(_Explorer* monitor, int x, int y, int heading) {
//   monitor->x = x;
//   monitor->y = y;
//   monitor->heading = heading;
//   // switch (monitor->state[MAIN]) {
//   //   default:
//   //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "drive", "DEFAULT");
//   //     break;
//   // }
//   // switch (monitor->state[EXPLORE]) {
//   //   case MOVE_EXPLORE:
//   //     if(x == monitor->x && y == monitor->y) {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     } else {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     }
//   //     break;
//   //   default:
//   //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "drive", "DEFAULT");
//   //     break;
//   // }
// }

// void raise_drive(_Explorer* monitor, int x, int y, int heading) {
//   param *p_head = NULL;
//   push_param(&p_head, &x, NULL, NULL, NULL);
//   push_param(&p_head, &y, NULL, NULL, NULL);
//   push_param(&p_head, &heading, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, DRIVE, p_head);
// }

// void turn(_Explorer* monitor, int facing) {
//   monitor->heading = facing;
//   // switch (monitor->state[MAIN]) {
//   //   default:
//   //     raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "turn", "DEFAULT");
//   //     break;
//   // }
//   // switch (monitor->state[EXPLORE]) {
//   //   case MOVE_EXPLORE:
//   //     if(facing != monitor->heading) {
//   //       monitor->state[EXPLORE] = LOOK_EXPLORE;
//   //     } else {
//   //       monitor->state[EXPLORE] = MOVE_EXPLORE;
//   //     }
//   //     break;
//   //   default:
//   //     raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "turn", "DEFAULT");
//   //     break;
//   // }
// }

// void raise_turn(_Explorer* monitor, int facing) {
//   param *p_head = NULL;
//   push_param(&p_head, &facing, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, TURN, p_head);
// }

// void scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) { //changed params from smedl
//   monitor->x = x;
//   monitor->y = y;
//   monitor->heading = heading;
//   set_view(monitor, map); //This raise needs to be immediate, not in queue
//   switch (monitor->state[MAIN]) {
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "view", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     case LOOK_EXPLORE:
//       if(contains_object(monitor)) {
//         raise_found(monitor);
//         monitor->state[EXPLORE] = MOVE_EXPLORE;
//       } else {
//         monitor->state[EXPLORE] = MOVE_EXPLORE;
//       }
//       break;
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "view", "DEFAULT");
//       break;
//   }
// }

// void raise_scan_view(_Explorer* monitor, int x, int y, int heading, const void* map) {
//   param *p_head = NULL;
//   push_param(&p_head, &x, NULL, NULL, NULL);
//   push_param(&p_head, &y, NULL, NULL, NULL);
//   push_action(&monitor->action_queue, SCAN_VIEW, p_head);
// }

// void found(_Explorer* monitor) {
//   switch (monitor->state[MAIN]) {
//     case EXPLORE_MAIN:
//       monitor->state[MAIN] = RETRIEVE_MAIN;
//       break;
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "found", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "found", "DEFAULT");
//       break;
//   }
// }

// void raise_found(_Explorer* monitor) {
//   param *p_head = NULL;
//   push_action(&monitor->action_queue, FOUND, p_head);
// }

// void retrieved(_Explorer* monitor) {
//   switch (monitor->state[MAIN]) {
//     case RETRIEVE_MAIN:
//       monitor->state[MAIN] = EXPLORE_MAIN;
//       break;
//     default:
//       raise_error("main", explorer_states_names[MAIN][monitor->state[MAIN]], "retrieved", "DEFAULT");
//       break;
//   }
//   switch (monitor->state[EXPLORE]) {
//     default:
//       raise_error("explore", explorer_states_names[EXPLORE][monitor->state[EXPLORE]], "retrieved", "DEFAULT");
//       break;
//   }
// }

// void raise_retrieved(_Explorer* monitor) {
//   param *p_head = NULL;
//   push_action(&monitor->action_queue, RETRIEVED, p_head);
// }

// void call_next_action(_Explorer *monitor) {
//   switch (monitor->action_queue->id) {
//     case DRIVE: ;
//       int x_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int y_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int heading_drive = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       drive(monitor, x_drive, y_drive, heading_drive);
//       break;
//     case TURN: ;
//       int facing_turn = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       turn(monitor, facing_turn);
//       break;
//     case SCAN_VIEW: ;
//       int x_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int y_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       int heading_view = monitor->action_queue->params->i;
//       pop_param(&monitor->action_queue->params);
//       const void *map_view = monitor->action_queue->params->v;
//       pop_param(&monitor->action_queue->params);
//       scan_view(monitor, x_view, y_view, heading_view, map_view);
//       break;
//     case FOUND: ;
//       found(monitor);
//       break;
//     case RETRIEVED: ;
//       retrieved(monitor);
//       break;
//   }
// }

// void exec_actions(_Explorer *monitor) {
//   while(monitor->action_queue != NULL) {
//     call_next_action(monitor);
//     pop_action(&monitor->action_queue);
//   }
// }

// void raise_error(char *scen, const char *state, char *action, char *type) {
//   printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}", scen, state, action, type);
// }


