//Compile: gcc -o stringVariableUpdate_mon -std=c99 actions.c monitor_map.c stringVariableUpdate_mon.c

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
#include "stringVariableUpdate_mon.h"

typedef enum { STRINGTEST_ID } stringtest_identity;
const identity_type stringtest_identity_types[STRINGTEST_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { STRINGTEST_SC1_SCENARIO, STRINGTEST_SC2_SCENARIO } stringtest_scenario;
typedef enum { STRINGTEST_SC1_START, STRINGTEST_SC1_END } stringtest_sc1_state;
typedef enum { STRINGTEST_SC2_START, STRINGTEST_SC2_END } stringtest_sc2_state;
typedef enum { STRINGTEST_PING_EVENT, STRINGTEST_TRANS_EVENT, STRINGTEST_PONG_EVENT } stringtest_event;
typedef enum { STRINGTEST_DEFAULT } stringtest_error;
const char *stringtest_sc1_states[2] = { "Start", "End" };
const char *stringtest_sc2_states[2] = { "Start", "End" };
const char **stringtest_states_names[2] = { stringtest_sc1_states, stringtest_sc2_states };
int executed_scenarios[2]={ 0,0 };

#define bindingkeyNum 1
#define msg_format_version "1.0.0"

StringtestMonitor* init_stringtest_monitor( StringtestData *d ) {
    StringtestMonitor* monitor = (StringtestMonitor*)malloc(sizeof(StringtestMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[STRINGTEST_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->name = d->name;
    monitor->value = d->value;
    monitor->state[STRINGTEST_SC1_SCENARIO] = STRINGTEST_SC1_START;
    monitor->state[STRINGTEST_SC2_SCENARIO] = STRINGTEST_SC2_START;
    monitor->action_queue = NULL;
    monitor->export_queue = NULL;

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(!config_read_file(&cfg, "stringVariableUpdate_mon.cfg")) {
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

    put_stringtest_monitor(monitor);
    return monitor;
}

void start_monitor(StringtestMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;

    // Announce that the monitor has started
    char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(strlen(ids)+50);
    sprintf(ann, "Stringtest monitor (%s) started.", ids);
    free(ids);
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->ctrl_exchange),
                                    amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                    0,
                                    0,
                                    NULL,
                                    amqp_cstring_bytes(ann)),
                "Publishing Stringtest monitor startup announcement");
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

                if (!strcmp(eventName,"ch1")) {
                    char *st;
                    int x = 0;
		cJSON * root = cJSON_Parse(string);
	char * msg_ver = cJSON_GetObjectItem(root,"fmt_version")->valuestring;
	 if(!strcmp(msg_ver,msg_format_version)){ 
		 cJSON * fmt = cJSON_GetObjectItem(root,"params");

st= cJSON_GetObjectItem(fmt,"v1")->valuestring;
	x= cJSON_GetObjectItem(fmt,"v2")->valueint;
	
                        stringtest_ping(monitor, st, x);
                        printf("stringtest_ping called.\n");
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

void send_message(StringtestMonitor* monitor, char* message, char* routing_key) {
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

void free_monitor(StringtestMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

//called at the end of each event handling function
void executeEvents(StringtestMonitor* monitor){
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

void executePendingEvents(StringtestMonitor* monitor){
    action** head = &monitor->action_queue;
    int i0; char* v0; 
    while(*head!=NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type){
            case STRINGTEST_TRANS_EVENT:
            		pop_param(&p_head);
		pop_action(head);
		stringtest_trans(monitor);

                break;
            case STRINGTEST_PONG_EVENT:
            		v0 = ((params)->v);
		(params) = (params)->next;
		i0 = ((params)->i);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		stringtest_pong(monitor, v0, i0);

                break;
            }
        pop_action(head);
    }
}

//send export events one by one from export_queue
void executeExportedEvent(StringtestMonitor* monitor){
    action** head = &monitor->export_queue;
    int i0; char* v0; 
    while(*head != NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type) {
            case STRINGTEST_PONG_EVENT:
            		v0 = ((params)->v);
		(params) = (params)->next;
		i0 = ((params)->i);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		exported_stringtest_pong(monitor, v0, i0);

                break;
            }
        pop_action(head);
    }

}


/*
 * Monitor Event Handlers
 */

void stringtest_ping(StringtestMonitor* monitor, char* st, int x) {
if (executed_scenarios[STRINGTEST_SC1_SCENARIO]==0) {
  switch (monitor->state[STRINGTEST_SC1_SCENARIO]) {
    case STRINGTEST_SC1_START:
        monitor->name = st;
        monitor->value = x;
        raise_stringtest_trans(monitor);
      monitor->state[STRINGTEST_SC1_SCENARIO] = STRINGTEST_SC1_END;
      break;

    default:
      raise_error("stringtest_sc1", stringtest_states_names[STRINGTEST_SC1_SCENARIO][monitor->state[STRINGTEST_SC1_SCENARIO]], "ping", "DEFAULT");
      break;
  }
executed_scenarios[STRINGTEST_SC1_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_stringtest_ping(StringtestMonitor* monitor, char* v0, int v1) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0);
  push_param(&p_head, &v1, NULL, NULL, NULL);
  push_action(&monitor->action_queue, STRINGTEST_PING_EVENT, p_head);
}


void stringtest_trans(StringtestMonitor* monitor) {
if (executed_scenarios[STRINGTEST_SC2_SCENARIO]==0) {
  switch (monitor->state[STRINGTEST_SC2_SCENARIO]) {
    case STRINGTEST_SC2_START:
        raise_stringtest_pong(monitor, monitor->name, monitor->value);
      monitor->state[STRINGTEST_SC2_SCENARIO] = STRINGTEST_SC2_END;
      break;

    default:
      raise_error("stringtest_sc2", stringtest_states_names[STRINGTEST_SC2_SCENARIO][monitor->state[STRINGTEST_SC2_SCENARIO]], "trans", "DEFAULT");
      break;
  }
executed_scenarios[STRINGTEST_SC2_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_stringtest_trans(StringtestMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, STRINGTEST_TRANS_EVENT, p_head);
}


void stringtest_pong(StringtestMonitor* monitor, char* name, int value) {
executeEvents(monitor);
}


void exported_stringtest_pong(StringtestMonitor* monitor , char* v0, int v1) {
  char* message;
	cJSON *root; cJSON* fmt;
	 root = cJSON_CreateObject();
	cJSON_AddItemToObject(root, "name", cJSON_CreateString("stringtest_pong"));
	cJSON_AddItemToObject(root, "fmt_version", cJSON_CreateString(msg_format_version));
	cJSON_AddItemToObject(root, "params", fmt = cJSON_CreateObject());

cJSON_AddStringToObject(fmt, "v1",v0);
cJSON_AddNumberToObject(fmt, "v2",v1);
message = cJSON_Print(root);

  char routing_key[256];
  sprintf(routing_key, "stringtest_pong.pong.0.%d", v1);
  send_message(monitor, message, routing_key);
}



void raise_stringtest_pong(StringtestMonitor* monitor, char* v0, int v1) {
  param *p_head = NULL;
 param *ep_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0);
  push_param(&ep_head, NULL, NULL, NULL, &v0);
  push_param(&p_head, &v1, NULL, NULL, NULL);
  push_param(&ep_head, &v1, NULL, NULL, NULL);
  push_action(&monitor->action_queue, STRINGTEST_PONG_EVENT, p_head);
  push_action(&monitor->export_queue, STRINGTEST_PONG_EVENT, ep_head);
}


/*
 * Monitor Utility Functions
 */

int init_stringtest_monitor_maps() {
    if (pthread_mutex_init(&stringtest_monitor_maps_lock, NULL) != 0) {
        printf("\nStringtest Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < STRINGTEST_MONITOR_IDENTITIES; i++) {
        stringtest_monitor_maps[i] = (StringtestMonitorMap*)malloc(sizeof(StringtestMonitorMap));
    }
    return 1;
}

void free_stringtest_monitor_maps() {
    // TODO
}

int add_stringtest_monitor_to_map(StringtestMonitor *monitor, int identity) {
    StringtestMonitorMap* map = stringtest_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, STRINGTEST_MONITOR_MAP_SIZE);
    StringtestMonitorRecord* record = (StringtestMonitorRecord*)malloc(sizeof(StringtestMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&stringtest_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&stringtest_monitor_maps_lock);
    return 1;
}

int put_stringtest_monitor(StringtestMonitor *monitor) {
    return add_stringtest_monitor_to_map(monitor, STRINGTEST_ID);
}

StringtestMonitorRecord* get_stringtest_monitors() {
    StringtestMonitorRecord* results = NULL;
    StringtestMonitorMap* map = stringtest_monitor_maps[0];
    for(int i = 0; i < STRINGTEST_MONITOR_MAP_SIZE; i++) {
        StringtestMonitorRecord* current = map->list[i];
        while(current != NULL) {
            StringtestMonitorRecord* record = (StringtestMonitorRecord*)malloc(sizeof(StringtestMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

StringtestMonitorRecord* get_stringtest_monitors_by_identity(int identity, int type, void *value) {
    StringtestMonitorRecord* results = NULL;
    StringtestMonitorMap* map = stringtest_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, STRINGTEST_MONITOR_MAP_SIZE);
    StringtestMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            StringtestMonitorRecord* record = (StringtestMonitorRecord*)malloc(sizeof(StringtestMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

StringtestMonitorRecord* filter_stringtest_monitors_by_identity(StringtestMonitorRecord* before, int identity, void  *value) {
    StringtestMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            StringtestMonitorRecord* record = (StringtestMonitorRecord*)malloc(sizeof(StringtestMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

char* monitor_identities_str(MonitorIdentity** identities) {
    char* out = malloc(20*STRINGTEST_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < STRINGTEST_MONITOR_IDENTITIES; i++) {
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