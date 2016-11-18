//Compile: gcc -o adaptationTrigger_mon -std=c99 actions.c monitor_map.c adaptationTrigger_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "amqp_utils.h"
#include "cJSON.h"
#include "mon_utils.h"
#include "adaptationTrigger_mon.h"
#include "helper.h"

typedef enum { ADAPTATIONTRIGGER_ID } adaptationtrigger_identity;
const identity_type adaptationtrigger_identity_types[ADAPTATIONTRIGGER_MONITOR_IDENTITIES] = { INT };

typedef enum { ADAPTATIONTRIGGER_COMPUTATION_SCENARIO } adaptationtrigger_scenario;
typedef enum { ADAPTATIONTRIGGER_COMPUTATION_START } adaptationtrigger_computation_state;
typedef enum { ADAPTATIONTRIGGER_WARNINGTHRESHOLD_EVENT, ADAPTATIONTRIGGER_ACTIVETRACKSTHRESHOLD_EVENT, ADAPTATIONTRIGGER_INPUTBYTESTHRESHOLD_EVENT, ADAPTATIONTRIGGER_ADAPTATIONCOMPLETE_EVENT, ADAPTATIONTRIGGER_EVAL_EVENT, ADAPTATIONTRIGGER_ADAPTATIONSTART_EVENT } adaptationtrigger_event;
typedef enum { ADAPTATIONTRIGGER_DEFAULT } adaptationtrigger_error;
const char *adaptationtrigger_computation_states[1] = { "Start" };
const char **adaptationtrigger_states_names[1] = { adaptationtrigger_computation_states };
int executed_scenarios[1]={ 0 };

#define bindingkeyNum 2
#define msg_format_version "1.0.0"

AdaptationtriggerMonitor* init_adaptationtrigger_monitor( AdaptationtriggerData *d ) {
    AdaptationtriggerMonitor* monitor = (AdaptationtriggerMonitor*)malloc(sizeof(AdaptationtriggerMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[ADAPTATIONTRIGGER_ID] = init_monitor_identity(INT, &d->id);
    monitor->Tw = d->Tw;
    monitor->Tat = d->Tat;
    monitor->Tib = d->Tib;
    monitor->enabled = d->enabled;
    monitor->TwID = d->TwID;
    monitor->TatID = d->TatID;
    monitor->TibID = d->TibID;
    monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
    monitor->action_queue = NULL;
    monitor->export_queue = NULL;

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(!config_read_file(&cfg, "adaptationTrigger_mon.cfg")) {
        output_config_error(cfg);
    }
    setting = config_lookup(&cfg, "rabbitmq");

    const char *hostname, *username, *password;
    int port = 0;

    if (setting != NULL) {
        if (!config_setting_lookup_string(setting, "hostname", &hostname) ||
            !config_setting_lookup_int(setting, "port", &port) ||
            !config_setting_lookup_string(setting, "username", &username) ||
            !config_setting_lookup_string(setting, "password", &password) ||
            !config_setting_lookup_string(setting, "exchange", &(monitor->amqp_exchange)) ||
            !config_setting_lookup_string(setting, "ctrl_exchange", &(monitor->ctrl_exchange))) {
                output_config_error(cfg);
        }
    }

    /* RabbitMQ initialization */
    amqp_bytes_t queuename;
    monitor->recv_conn = amqp_new_connection();
    monitor->recv_socket = amqp_tcp_socket_new(monitor->recv_conn);
    if (!monitor->recv_socket) {
        die("creating TCP socket");
    }
    int status = amqp_socket_open(monitor->recv_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    die_on_amqp_error(amqp_login(monitor->recv_conn, "/", 0, 131072, 0,
        AMQP_SASL_METHOD_PLAIN, username, password), "Logging in");
    amqp_channel_open(monitor->recv_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Opening channel");
    amqp_queue_declare_ok_t *r = amqp_queue_declare(monitor->recv_conn, 1,
        amqp_empty_bytes, 0, 0, 0, 1, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Declaring queue");
    queuename = amqp_bytes_malloc_dup(r->queue);
    if (queuename.bytes == NULL) {
        fprintf(stderr, "Out of memory while copying queue name");
        exit(EXIT_FAILURE);
    }

    monitor->send_conn = amqp_new_connection();
    monitor->send_socket = amqp_tcp_socket_new(monitor->send_conn);
    if (!monitor->send_socket) {
        die("creating TCP socket");
    }
    status = amqp_socket_open(monitor->send_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    die_on_amqp_error(amqp_login(monitor->send_conn, "/", 0, 131072, 0,
        AMQP_SASL_METHOD_PLAIN, username, password), "Logging in");
    amqp_channel_open(monitor->send_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn),
        "Opening channel");
    amqp_exchange_declare(monitor->send_conn, 1,
        amqp_cstring_bytes(monitor->amqp_exchange),
        amqp_cstring_bytes("topic"), 0, 1, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn),
        "Declaring primary exchange");
    amqp_exchange_declare(monitor->send_conn, 1,
        amqp_cstring_bytes(monitor->ctrl_exchange),
        amqp_cstring_bytes("fanout"), 0, 1, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn),
        "Declaring control exchange");

    // binding several binding keys
    char ** bindingkeys = (char**)malloc(bindingkeyNum*sizeof(char*));
    bindingkeys[0]=(char*)malloc(255*sizeof(char));
	strcpy(bindingkeys[0],"ch2");
strcat(bindingkeys[0],".#");
bindingkeys[1]=(char*)malloc(255*sizeof(char));
	strcpy(bindingkeys[1],"ch6");
strcat(bindingkeys[1],".#");


    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(monitor->amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");

    put_adaptationtrigger_monitor(monitor);
    return monitor;
}

void start_monitor(AdaptationtriggerMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;

    // Announce that the monitor has started
    char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(strlen(ids)+50);
    sprintf(ann, "Adaptationtrigger monitor (%s) started.", ids);
    free(ids);
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->ctrl_exchange),
                                    amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                    0,
                                    0,
                                    NULL,
                                    amqp_cstring_bytes(ann)),
                "Publishing Adaptationtrigger monitor startup announcement");
    free(ann);

    while (1) {
        amqp_rpc_reply_t ret;
        amqp_envelope_t envelope;
        amqp_maybe_release_buffers(monitor->recv_conn);
        ret = amqp_consume_message(monitor->recv_conn, &envelope, NULL, 0);
        amqp_message_t msg = envelope.message;
        amqp_bytes_t bytes = msg.body;
        amqp_bytes_t routing_key = envelope.routing_key;
        char* rk = (char*)routing_key.bytes;
        char* string = (char*)bytes.bytes;
        //char* event[255] = {NULL};

        if (string != NULL) {
            char* eventName = strtok(rk, ".");
            if (eventName != NULL) {
                char e[255];

                if (!strcmp(eventName,"ch2")) {
                    char *id;
                    int val = 0;
		cJSON * root = cJSON_Parse(string);
	char * msg_ver = cJSON_GetObjectItem(root,"fmt_version")->valuestring;
	 if(!strcmp(msg_ver,msg_format_version)){ 
		 cJSON * fmt = cJSON_GetObjectItem(root,"params");

id= cJSON_GetObjectItem(fmt,"v1")->valuestring;
	val= cJSON_GetObjectItem(fmt,"v2")->valueint;
	
                        adaptationtrigger_warningThreshold(monitor, id, val);
                        printf("adaptationtrigger_warningThreshold called.\n");
                    }
	 else {
	 printf("format version not matched\n");
	}
                }
                else if (!strcmp(eventName,"ch6")) {
		cJSON * root = cJSON_Parse(string);
	char * msg_ver = cJSON_GetObjectItem(root,"fmt_version")->valuestring;
	 if(!strcmp(msg_ver,msg_format_version)){ 
	

                        adaptationtrigger_adaptationComplete(monitor);
                        printf("adaptationtrigger_adaptationComplete called.\n");
                    }
	 else {
	 printf("format version not matched\n");
	}
                }

            }
            //free(eventName);
        }

        if (AMQP_RESPONSE_NORMAL != ret.reply_type) {
            if (AMQP_RESPONSE_LIBRARY_EXCEPTION == ret.reply_type &&
                AMQP_STATUS_UNEXPECTED_STATE == ret.library_error) {
                if (AMQP_STATUS_OK != amqp_simple_wait_frame(monitor->recv_conn, &frame)) {
                    return;
                }

                if (AMQP_FRAME_METHOD == frame.frame_type) {
                    switch (frame.payload.method.id) {
                        case AMQP_BASIC_ACK_METHOD:
                            /* if we've turned publisher confirms on, and we've published a message
                             * here is a message being confirmed
                             */
                            printf("AMQP_BASIC_ACK_METHOD\n");
                            break;
                        case AMQP_BASIC_RETURN_METHOD:
                            /* if a published message couldn't be routed and the mandatory flag was set
                             * this is what would be returned. The message then needs to be read.
                             */
                            printf("AMQP_BASIC_RETURN_METHOD\n");
                            amqp_message_t message;
                            ret = amqp_read_message(monitor->recv_conn, frame.channel, &message, 0);
                            if (AMQP_RESPONSE_NORMAL != ret.reply_type) {
                                return;
                            }
                            amqp_destroy_message(&message);
                            break;

                        case AMQP_CHANNEL_CLOSE_METHOD:
                            /* a channel.close method happens when a channel exception occurs, this
                             * can happen by publishing to an exchange that doesn't exist for example
                             *
                             * In this case you would need to open another channel redeclare any queues
                             * that were declared auto-delete, and restart any consumers that were attached
                             * to the previous channel
                             */
                            return;

                        case AMQP_CONNECTION_CLOSE_METHOD:
                            /* a connection.close method happens when a connection exception occurs,
                             * this can happen by trying to use a channel that isn't open for example.
                             *
                             * In this case the whole connection must be restarted.
                             */
                            return;

                        default:
                            fprintf(stderr ,"An unexpected method was received %u\n", frame.payload.method.id);
                            return;
                    }
                }
            }
        } else {
            amqp_destroy_envelope(&envelope);
        }
        received++;
    }
}

void send_message(AdaptationtriggerMonitor* monitor, char* message, char* routing_key) {
    amqp_bytes_t message_bytes;
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    amqp_bytes_t routingkey_bytes;
    routingkey_bytes.len = strlen(routing_key)+1;
    routingkey_bytes.bytes = routing_key;
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->amqp_exchange),
                                    routingkey_bytes,
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                 "Publishing");

}

void free_monitor(AdaptationtriggerMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

//called at the end of each event handling function
void executeEvents(AdaptationtriggerMonitor* monitor){
    if(monitor->action_queue != NULL){
        executePendingEvents(monitor);
    }

    if(monitor->action_queue == NULL && monitor->export_queue != NULL){
        executeExportedEvent(monitor);
    }
    if(monitor->action_queue == NULL && monitor->export_queue == NULL){
        memset(executed_scenarios, 0, sizeof(executed_scenarios));
    }

}

void executePendingEvents(AdaptationtriggerMonitor* monitor){
    action** head = &monitor->action_queue;
    int i0; char* v0; 
    while(*head!=NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type){
            case ADAPTATIONTRIGGER_EVAL_EVENT:
            		pop_param(&p_head);
		pop_action(head);
		adaptationtrigger_eval(monitor);

                break;
            case ADAPTATIONTRIGGER_ADAPTATIONSTART_EVENT:
            		pop_param(&p_head);
		pop_action(head);
		adaptationtrigger_adaptationStart(monitor);

                break;
            }
        pop_action(head);
    }
}

//send export events one by one from export_queue
void executeExportedEvent(AdaptationtriggerMonitor* monitor){
    action** head = &monitor->export_queue;
    int i0; char* v0; 
    while(*head != NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type) {
            case ADAPTATIONTRIGGER_ADAPTATIONSTART_EVENT:
            		pop_param(&p_head);
		pop_action(head);
		exported_adaptationtrigger_adaptationStart(monitor);

                break;
            }
        pop_action(head);
    }

}


/*
 * Monitor Event Handlers
 */

void adaptationtrigger_warningThreshold(AdaptationtriggerMonitor* monitor, char* id, int val) {
if (executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]) {
    case ADAPTATIONTRIGGER_COMPUTATION_START:
      if(compare(id, monitor->TwID)) {
        monitor->Tw = val;
        raise_adaptationtrigger_eval(monitor);
        monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      }
      else if(compare(id, monitor->TatID)) {
        monitor->Tat = val;
        raise_adaptationtrigger_eval(monitor);
        monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      }
      else if(compare(id, monitor->TibID)) {
        monitor->Tib = val;
        raise_adaptationtrigger_eval(monitor);
        monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      }
      else {
        raise_error("computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("adaptationtrigger_computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "warningThreshold", "DEFAULT");
      break;
  }
executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_adaptationtrigger_warningThreshold(AdaptationtriggerMonitor* monitor, char* v0, int v1) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0);
  push_param(&p_head, &v1, NULL, NULL, NULL);
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_WARNINGTHRESHOLD_EVENT, p_head);
}


void adaptationtrigger_activeTracksThreshold(AdaptationtriggerMonitor* monitor, int val) {
if (executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]) {
    case ADAPTATIONTRIGGER_COMPUTATION_START:
        monitor->Tat = val;
        raise_adaptationtrigger_eval(monitor);
      monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      break;

    default:
      raise_error("adaptationtrigger_computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "activeTracksThreshold", "DEFAULT");
      break;
  }
executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_adaptationtrigger_activeTracksThreshold(AdaptationtriggerMonitor* monitor, int v0) {
  param *p_head = NULL;
  push_param(&p_head, &v0, NULL, NULL, NULL);
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_ACTIVETRACKSTHRESHOLD_EVENT, p_head);
}


void adaptationtrigger_inputBytesThreshold(AdaptationtriggerMonitor* monitor, int val) {
if (executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]) {
    case ADAPTATIONTRIGGER_COMPUTATION_START:
        monitor->Tib = val;
        raise_adaptationtrigger_eval(monitor);
      monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      break;

    default:
      raise_error("adaptationtrigger_computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "inputBytesThreshold", "DEFAULT");
      break;
  }
executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_adaptationtrigger_inputBytesThreshold(AdaptationtriggerMonitor* monitor, int v0) {
  param *p_head = NULL;
  push_param(&p_head, &v0, NULL, NULL, NULL);
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_INPUTBYTESTHRESHOLD_EVENT, p_head);
}


void adaptationtrigger_adaptationComplete(AdaptationtriggerMonitor* monitor) {
if (executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]) {
    case ADAPTATIONTRIGGER_COMPUTATION_START:
        monitor->enabled = 1;
      monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      break;

    default:
      raise_error("adaptationtrigger_computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "adaptationComplete", "DEFAULT");
      break;
  }
executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_adaptationtrigger_adaptationComplete(AdaptationtriggerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_ADAPTATIONCOMPLETE_EVENT, p_head);
}


void adaptationtrigger_eval(AdaptationtriggerMonitor* monitor) {
if (executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]) {
    case ADAPTATIONTRIGGER_COMPUTATION_START:
      if(monitor->enabled == 1 && monitor->Tw != 0 && monitor->Tat != 0 && monitor->Tib == 0) {
        monitor->enabled = 0;
        monitor->Tw = 0;
        monitor->Tat = 0;
        raise_adaptationtrigger_adaptationStart(monitor);
        monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO] = ADAPTATIONTRIGGER_COMPUTATION_START;
      }
      else {
        raise_error("computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("adaptationtrigger_computation", adaptationtrigger_states_names[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO][monitor->state[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]], "eval", "DEFAULT");
      break;
  }
executed_scenarios[ADAPTATIONTRIGGER_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_adaptationtrigger_eval(AdaptationtriggerMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_EVAL_EVENT, p_head);
}


void adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor) {
executeEvents(monitor);
}


void exported_adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor ) {
  char* message;
	cJSON *root; cJSON* fmt;
	 root = cJSON_CreateObject();
	cJSON_AddItemToObject(root, "name", cJSON_CreateString("adaptationtrigger_adaptationStart"));
	cJSON_AddItemToObject(root, "fmt_version", cJSON_CreateString(msg_format_version));
	cJSON_AddItemToObject(root, "params", fmt = cJSON_CreateObject());

message = cJSON_Print(root);

  char routing_key[256];
  sprintf(routing_key, "adaptationTrigger_adaptationStart.%ld.adaptationStart", (long)(*(int*)(monitor->identities[ADAPTATIONTRIGGER_ID]->value)));
  send_message(monitor, message, routing_key);
}



void raise_adaptationtrigger_adaptationStart(AdaptationtriggerMonitor* monitor) {
  param *p_head = NULL;
 param *ep_head = NULL;
  push_action(&monitor->action_queue, ADAPTATIONTRIGGER_ADAPTATIONSTART_EVENT, p_head);
  push_action(&monitor->export_queue, ADAPTATIONTRIGGER_ADAPTATIONSTART_EVENT, ep_head);
}


/*
 * Monitor Utility Functions
 */

int init_adaptationtrigger_monitor_maps() {
    if (pthread_mutex_init(&adaptationtrigger_monitor_maps_lock, NULL) != 0) {
        printf("\nAdaptationtrigger Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < ADAPTATIONTRIGGER_MONITOR_IDENTITIES; i++) {
        adaptationtrigger_monitor_maps[i] = (AdaptationtriggerMonitorMap*)malloc(sizeof(AdaptationtriggerMonitorMap));
    }
    return 1;
}

void free_adaptationtrigger_monitor_maps() {
    // TODO
}

int add_adaptationtrigger_monitor_to_map(AdaptationtriggerMonitor *monitor, int identity) {
    AdaptationtriggerMonitorMap* map = adaptationtrigger_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, ADAPTATIONTRIGGER_MONITOR_MAP_SIZE);
    AdaptationtriggerMonitorRecord* record = (AdaptationtriggerMonitorRecord*)malloc(sizeof(AdaptationtriggerMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&adaptationtrigger_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&adaptationtrigger_monitor_maps_lock);
    return 1;
}

int put_adaptationtrigger_monitor(AdaptationtriggerMonitor *monitor) {
    return add_adaptationtrigger_monitor_to_map(monitor, ADAPTATIONTRIGGER_ID);
}

AdaptationtriggerMonitorRecord* get_adaptationtrigger_monitors() {
    AdaptationtriggerMonitorRecord* results = NULL;
    AdaptationtriggerMonitorMap* map = adaptationtrigger_monitor_maps[0];
    for(int i = 0; i < ADAPTATIONTRIGGER_MONITOR_MAP_SIZE; i++) {
        AdaptationtriggerMonitorRecord* current = map->list[i];
        while(current != NULL) {
            AdaptationtriggerMonitorRecord* record = (AdaptationtriggerMonitorRecord*)malloc(sizeof(AdaptationtriggerMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

AdaptationtriggerMonitorRecord* get_adaptationtrigger_monitors_by_identity(int identity, int type, void *value) {
    AdaptationtriggerMonitorRecord* results = NULL;
    AdaptationtriggerMonitorMap* map = adaptationtrigger_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, ADAPTATIONTRIGGER_MONITOR_MAP_SIZE);
    AdaptationtriggerMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            AdaptationtriggerMonitorRecord* record = (AdaptationtriggerMonitorRecord*)malloc(sizeof(AdaptationtriggerMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

AdaptationtriggerMonitorRecord* filter_adaptationtrigger_monitors_by_identity(AdaptationtriggerMonitorRecord* before, int identity, void  *value) {
    AdaptationtriggerMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            AdaptationtriggerMonitorRecord* record = (AdaptationtriggerMonitorRecord*)malloc(sizeof(AdaptationtriggerMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

char* monitor_identities_str(MonitorIdentity** identities) {
    char* out = malloc(20*ADAPTATIONTRIGGER_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < ADAPTATIONTRIGGER_MONITOR_IDENTITIES; i++) {
        char* monid_str = monitor_identity_str(identities[i]);
        if (i == 0) {
            strcat(out, monid_str);
        }
        else {
            strcat(out, ", ");
            strcat(out, monid_str);
        }
        free(monid_str);
    }
    return out;
}