//Compile: gcc -o json_mon -std=c99 actions.c monitor_map.c json_mon.c

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
#include "json_mon.h"

typedef enum { JSONTEST_ID } jsontest_identity;
const identity_type jsontest_identity_types[JSONTEST_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { JSONTEST_SC1_SCENARIO } jsontest_scenario;
typedef enum { JSONTEST_SC1_START, JSONTEST_SC1_END } jsontest_sc1_state;
typedef enum { JSONTEST_PING_EVENT, JSONTEST_PONG_EVENT } jsontest_event;
typedef enum { JSONTEST_DEFAULT } jsontest_error;
const char *jsontest_sc1_states[2] = { "Start", "End" };
const char **jsontest_states_names[1] = { jsontest_sc1_states };
int executed_scenarios[1]={ 0 };

#define bindingkeyNum 1
#define msg_format_version "1.0.0"

JsontestMonitor* init_jsontest_monitor( JsontestData *d ) {
    JsontestMonitor* monitor = (JsontestMonitor*)malloc(sizeof(JsontestMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[JSONTEST_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->state[JSONTEST_SC1_SCENARIO] = JSONTEST_SC1_START;
    monitor->action_queue = NULL;
    monitor->export_queue = NULL;

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(!config_read_file(&cfg, "json_mon.cfg")) {
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
	strcpy(bindingkeys[0],"ch1");
strcat(bindingkeys[0],".#");


    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(monitor->amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");

    put_jsontest_monitor(monitor);
    return monitor;
}

void start_monitor(JsontestMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;

    // Announce that the monitor has started
    char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(strlen(ids)+50);
    sprintf(ann, "Jsontest monitor (%s) started.", ids);
    free(ids);
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->ctrl_exchange),
                                    amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                    0,
                                    0,
                                    NULL,
                                    amqp_cstring_bytes(ann)),
                "Publishing Jsontest monitor startup announcement");
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

        if (string != NULL) {
            char* eventName = strtok(rk, ".");
            if (eventName != NULL) {

                if (!strcmp(eventName,"ch1")) {
                    char *st;
                    int i = 0;
                    double f = 0;
		cJSON * root = cJSON_Parse(string);
	char * msg_ver = cJSON_GetObjectItem(root,"fmt_version")->valuestring;
	 if(!strcmp(msg_ver,msg_format_version)){ 
		 cJSON * fmt = cJSON_GetObjectItem(root,"params");

st= cJSON_GetObjectItem(fmt,"v1")->valuestring;
	i= cJSON_GetObjectItem(fmt,"v2")->valueint;
	f= cJSON_GetObjectItem(fmt,"v3")->valuedouble;
	
                        jsontest_ping(monitor, st, i, f);
                        printf("jsontest_ping called.\n");
                    }
	 else {
	 printf("format version not matched\n");
	}
                }

            }
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

void send_message(JsontestMonitor* monitor, char* message, char* routing_key) {
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

void free_monitor(JsontestMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

//called at the end of each event handling function
void executeEvents(JsontestMonitor* monitor){
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

void executePendingEvents(JsontestMonitor* monitor){
    action** head = &monitor->action_queue;
    int i0; double d0; char* v0; 
    while(*head!=NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type){
            case JSONTEST_PONG_EVENT:
            		d0 = ((params)->d);
		(params) = (params)->next;
		i0 = ((params)->i);
		(params) = (params)->next;
		v0 = ((params)->v);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		jsontest_pong(monitor, d0, i0, v0);

                break;
            }
        pop_action(head);
    }
}

//send export events one by one from export_queue
void executeExportedEvent(JsontestMonitor* monitor){
    action** head = &monitor->export_queue;
    int i0; double d0; char* v0; 
    while(*head != NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type) {
            case JSONTEST_PONG_EVENT:
            		d0 = ((params)->d);
		(params) = (params)->next;
		i0 = ((params)->i);
		(params) = (params)->next;
		v0 = ((params)->v);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		exported_jsontest_pong(monitor, d0, i0, v0);

                break;
            }
        pop_action(head);
    }

}


/*
 * Monitor Event Handlers
 */

void jsontest_ping(JsontestMonitor* monitor, char* st, int i, double f) {
if (executed_scenarios[JSONTEST_SC1_SCENARIO]==0) {
  switch (monitor->state[JSONTEST_SC1_SCENARIO]) {
    case JSONTEST_SC1_START:
        raise_jsontest_pong(monitor, f, i, st);
      monitor->state[JSONTEST_SC1_SCENARIO] = JSONTEST_SC1_END;
      break;

    default:
      raise_error("jsontest_sc1", jsontest_states_names[JSONTEST_SC1_SCENARIO][monitor->state[JSONTEST_SC1_SCENARIO]], "ping", "DEFAULT");
      break;
  }
executed_scenarios[JSONTEST_SC1_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_jsontest_ping(JsontestMonitor* monitor, char* v0, int v1, double v2) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0);
  push_param(&p_head, &v1, NULL, NULL, NULL);
  push_param(&p_head, NULL, NULL, &v2, NULL);
  push_action(&monitor->action_queue, JSONTEST_PING_EVENT, p_head);
}


void jsontest_pong(JsontestMonitor* monitor, double f, int i, char* st) {
executeEvents(monitor);
}


void exported_jsontest_pong(JsontestMonitor* monitor , double v0, int v1, char* v2) {
  char* message;
	cJSON *root; cJSON* fmt;
	 root = cJSON_CreateObject();
	cJSON_AddItemToObject(root, "name", cJSON_CreateString("jsontest_pong"));
	cJSON_AddItemToObject(root, "fmt_version", cJSON_CreateString(msg_format_version));
	cJSON_AddItemToObject(root, "params", fmt = cJSON_CreateObject());

cJSON_AddNumberToObject(fmt, "v1",v0);
cJSON_AddNumberToObject(fmt, "v2",v1);
cJSON_AddStringToObject(fmt, "v3",v2);
message = cJSON_Print(root);

  char routing_key[256];
  sprintf(routing_key, "jsontest_pong.pong.0.%d.0", v1);
  send_message(monitor, message, routing_key);
}



void raise_jsontest_pong(JsontestMonitor* monitor, double v0, int v1, char* v2) {
  param *p_head = NULL;
 param *ep_head = NULL;
  push_param(&p_head, NULL, NULL, &v0, NULL);
  push_param(&ep_head, NULL, NULL, &v0, NULL);
  push_param(&p_head, &v1, NULL, NULL, NULL);
  push_param(&ep_head, &v1, NULL, NULL, NULL);
  push_param(&p_head, NULL, NULL, NULL, &v2);
  push_param(&ep_head, NULL, NULL, NULL, &v2);
  push_action(&monitor->action_queue, JSONTEST_PONG_EVENT, p_head);
  push_action(&monitor->export_queue, JSONTEST_PONG_EVENT, ep_head);
}


/*
 * Monitor Utility Functions
 */

int init_jsontest_monitor_maps() {
    if (pthread_mutex_init(&jsontest_monitor_maps_lock, NULL) != 0) {
        printf("\nJsontest Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < JSONTEST_MONITOR_IDENTITIES; i++) {
        jsontest_monitor_maps[i] = (JsontestMonitorMap*)malloc(sizeof(JsontestMonitorMap));
    }
    return 1;
}

void free_jsontest_monitor_maps() {
    // TODO
}

int add_jsontest_monitor_to_map(JsontestMonitor *monitor, int identity) {
    JsontestMonitorMap* map = jsontest_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, JSONTEST_MONITOR_MAP_SIZE);
    JsontestMonitorRecord* record = (JsontestMonitorRecord*)malloc(sizeof(JsontestMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&jsontest_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&jsontest_monitor_maps_lock);
    return 1;
}

int put_jsontest_monitor(JsontestMonitor *monitor) {
    return add_jsontest_monitor_to_map(monitor, JSONTEST_ID);
}

JsontestMonitorRecord* get_jsontest_monitors() {
    JsontestMonitorRecord* results = NULL;
    JsontestMonitorMap* map = jsontest_monitor_maps[0];
    for(int i = 0; i < JSONTEST_MONITOR_MAP_SIZE; i++) {
        JsontestMonitorRecord* current = map->list[i];
        while(current != NULL) {
            JsontestMonitorRecord* record = (JsontestMonitorRecord*)malloc(sizeof(JsontestMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

JsontestMonitorRecord* get_jsontest_monitors_by_identity(int identity, int type, void *value) {
    JsontestMonitorRecord* results = NULL;
    JsontestMonitorMap* map = jsontest_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, JSONTEST_MONITOR_MAP_SIZE);
    JsontestMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            JsontestMonitorRecord* record = (JsontestMonitorRecord*)malloc(sizeof(JsontestMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

JsontestMonitorRecord* filter_jsontest_monitors_by_identity(JsontestMonitorRecord* before, int identity, void  *value) {
    JsontestMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            JsontestMonitorRecord* record = (JsontestMonitorRecord*)malloc(sizeof(JsontestMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

char* monitor_identities_str(MonitorIdentity** identities) {
    char* out = malloc(20*JSONTEST_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < JSONTEST_MONITOR_IDENTITIES; i++) {
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