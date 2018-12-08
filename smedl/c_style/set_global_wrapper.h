#ifndef {{ sync_set_name|upper }}_GLOBAL_WRAPPER_H
#define {{ sync_set_name|upper }}_GLOBAL_WRAPPER_H

#include "monitor_map.h"
#include "actions.h"

#define bindingkeyNum {{ bindingkeys_num }}
#define msg_format_version "1.0.0"

typedef enum { {{ sync_set_monitors_enum }} } {{ sync_set_name }}_Monitor_Type;
{% if genjson == False -%}
typedef enum {
    {%- for c in sync_set_connections -%}
    {{ sync_set_name|upper }}_{{ c|upper }}_CONNECTION{{ ", " if not loop.last }}
    {%- endfor -%}
} {{ sync_set_name }}_Connection;
{% endif -%}

// The global wrapper export API. All exported events go through this function, which sorts them
// into the sync queue, async queue, or both, depending on which monitors they go to.
void export_event(int monitor_type, MonitorIdentity *identities[], int event_id, param *params);

{% if genjson -%}
// Send a message over RabbitMQ. This is used by the exported_...() functions in
// the monitors.
void send_message(char* message, char* routing_key);

// Split the routing key rk up into parts at each dot and return array of the first argNum parts
char** divideRoutingkey(char * rk, int argNum);

{% endif -%}
// Get the parameter at index idx from the provided parameter list
param* get_param_by_idx(param * head, int idx);

{% if genjson -%}
// Moved from <monitortype>_mon.c but not currently used.
smedl_provenance_t* create_provenance_object(char event[], int line, long trace_counter);

{% endif -%}
{% if genjson == False -%}
// Initialize the monitors in the set
void {{ sync_set_name|lower }}_set_init();

// Synchronously import an event into the global wrapper
void {{ sync_set_name|lower }}_global_import({{ sync_set_name }}_Connection ch_id, param *params);

// Handle all the events that have accumulated in the sync and async queues
// (called by {{ sync_set_name|lower }}_global_import()
void {{ sync_set_name|lower }}_process_queues();

{% endif -%}
#endif //{{ sync_set_name|upper }}_GLOBAL_WRAPPER_H
