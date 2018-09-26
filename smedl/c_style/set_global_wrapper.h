#ifndef {{ sync_set_name|upper }}_GLOBAL_WRAPPER_H
#define {{ sync_set_name|upper }}_GLOBAL_WRAPPER_H

#include "monitor_map.h"
#include "actions.h"

#define bindingkeyNum {{ bindingkeys_num }}
#define msg_format_version "1.0.0"

typedef enum { {{ sync_set_monitors_enum }} } {{ sync_set_name }}_Monitor_Type;

// The global wrapper export API. All exported events go through this function, which sorts them
// into the sync queue, async queue, or both, depending on which monitors they go to.
void export_event(int monitor_type, MonitorIdentity *identities[], int event_id, param *params);

// Send a message over RabbitMQ. This is used by the exported_...() functions in
// the monitors.
void send_message(char* message, char* routing_key);

// Split the routing key rk up into parts at each dot and return array of the first argNum parts
char** divideRoutingkey(char * rk, int argNum);

// Get the parameter at index idx from the provided parameter list
param* get_param_by_idx(param * head, int idx);

// Moved from <monitortype>_mon.c but not currently used.
smedl_provenance_t* create_provenance_object(char event[], int line, long trace_counter);

#endif //{{ sync_set_name|upper }}_GLOBAL_WRAPPER_H
