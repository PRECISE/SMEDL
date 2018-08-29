#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "mon_utils.h"
#include "cJSON.h"
#include "{{ base_file_name }}_mon.h"
#define bindingkeyNum {{ bindingkeys_num }}

// This function handles imported events.
// The first 4 parameters align with get_{{ obj|lower }}_monitors_by_identities. If there are no identities to match,
// they should be NULL, 0, NULL, 0 (although it doesn't really matter).
// event_id is from the {{ obj|lower }}_event enum
// params are the parameters of the event
void import_event_{{ obj|lower }}(int identity[], int type, coid *values[], int size, int event_id, param *params) {
    {{ obj|title }}MonitorRecord* record;
    // Get the relevant monitor instances. Filter by ID or do dynamic instantiation if needed
    // (depends on the event type)
    switch (event_id) { //One case for each imported event.
        {% for in imported_event_case -%}
        case {{ e.event_enum|join('\n') }}
        {{e.callstring}}
            break;
        {% endfor -%}
    }
}

// Handle events to be exported to RabbitMQ from the global wrapper.
void export_async_event_{{ obj }}(MonitorIdentity** identities, int event_id, param *params) {
    param *p_head = params;

    switch (event_id) {
        // Only need cases for exported events that go outside the synchronous set
        // Parse out the appropriate parameters for the event type and call the appropriate
        //   function for that event to generate the JSON and send it
        {% for in exported_async_event_case -%}
        case {{ e.event_enum|join('\n') }}
        {{e.callstring}}
            break;
        {% endfor -%}
    }
}
