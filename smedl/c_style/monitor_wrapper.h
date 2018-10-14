#ifndef {{ base_file_name|upper }}_MONITOR_WRAPPER_H
#define {{ base_file_name|upper }}_MONITOR_WRAPPER_H

// Called by the global wrapper to handle incoming events. It dispatches them to the appropriate instance
// and performs dynamic instantiation if necessary.
// The first 4 parameters align with get_{{ obj|lower }}_monitors_by_identities. If there are no identities to match,
// they should be NULL, 0, NULL, 0 (although it doesn't really matter).
// event_id is from the {{ obj|lower }}_event enum
// params are the parameters of the event
void import_event_{{ obj|lower }}(int identity[], int type, void *values[], int size, int event_id, param *params);

// Called by the global wrapper when it needs to export events to RabbitMQ. It calls the appropriate
// exported_<monitortype>_<eventname>() function to generate the JSON and send the message.
void export_async_event_{{ obj|lower }}(MonitorIdentity** identities, int event_id, param *params);


#endif //{{ base_file_name|upper }}_MONITOR_WRAPPER_H
