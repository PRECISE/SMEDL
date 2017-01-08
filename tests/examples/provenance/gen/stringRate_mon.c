//Compile: gcc -o stringRate_mon -std=c99 actions.c monitor_map.c stringRate_mon.c

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
#include "stringRate_mon.h"
#include "helper.h"

typedef enum { RATECOMPUTATION_ID } ratecomputation_identity;
const identity_type ratecomputation_identity_types[RATECOMPUTATION_MONITOR_IDENTITIES] = { INT };

typedef enum { RATECOMPUTATION_COMPUTATION_SCENARIO } ratecomputation_scenario;
typedef enum { RATECOMPUTATION_COMPUTATION_INIT, RATECOMPUTATION_COMPUTATION_END, RATECOMPUTATION_COMPUTATION_COMPUTERATE } ratecomputation_computation_state;
typedef enum { RATECOMPUTATION_DATAUPDATE_EVENT, RATECOMPUTATION_TIMEOUT_EVENT, RATECOMPUTATION_END_EVENT, RATECOMPUTATION_DATAUPDATE2_EVENT } ratecomputation_event;
typedef enum { RATECOMPUTATION_DEFAULT } ratecomputation_error;
const char *ratecomputation_computation_states[3] = { "Init", "End", "ComputeRate" };
const char **ratecomputation_states_names[1] = { ratecomputation_computation_states };
int executed_scenarios[1]={ 0 };

#define bindingkeyNum 3
#define msg_format_version "1.0.0"

RatecomputationMonitor* init_ratecomputation_monitor( RatecomputationData *d ) {
    RatecomputationMonitor* monitor = (RatecomputationMonitor*)malloc(sizeof(RatecomputationMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[RATECOMPUTATION_ID] = init_monitor_identity(INT, &d->id);
    monitor->lastTime = d->lastTime;
    monitor->curTime = d->curTime;
    monitor->sum = d->sum;
    monitor->name = d->name;
    monitor->rate = d->rate;
    monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_INIT;
    monitor->action_queue = NULL;
    monitor->export_queue = NULL;

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(!config_read_file(&cfg, "stringRate_mon.cfg")) {
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
	strcpy(bindingkeys[0],"ch3");
strcat(bindingkeys[0],".#");
bindingkeys[1]=(char*)malloc(255*sizeof(char));
	strcpy(bindingkeys[1],"ch4");
strcat(bindingkeys[1],".#");
bindingkeys[2]=(char*)malloc(255*sizeof(char));
	strcpy(bindingkeys[2],"ch5");
strcat(bindingkeys[2],".#");


    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(monitor->amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");

    put_ratecomputation_monitor(monitor);
    return monitor;
}

smedl_provenance_t* create_provenance_object(char event[255], int line, long trace_counter){
    smedl_provenance_t* provenance = (smedl_provenance_t*)malloc(sizeof(smedl_provenance_t));
    strncpy(provenance -> event, event,255);
    provenance -> line = line;
    provenance -> trace_counter = trace_counter;
    return provenance;
}

void start_monitor(RatecomputationMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;

    // Announce that the monitor has started
    char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(strlen(ids)+50);
    sprintf(ann, "Ratecomputation monitor (%s) started.", ids);
    free(ids);
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->ctrl_exchange),
                                    amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                    0,
                                    0,
                                    NULL,
                                    amqp_cstring_bytes(ann)),
                "Publishing Ratecomputation monitor startup announcement");
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
                cJSON * root = cJSON_Parse(string);
                cJSON * ver = cJSON_GetObjectItem(root,"fmt_version");
                char * msg_ver = NULL;
                if(ver!=NULL){
                    msg_ver = ver->valuestring;
                }
                cJSON* pro = NULL;
                if(!strcmp(msg_ver,msg_format_version)){
                    pro = cJSON_GetObjectItem(root,"provenance");
                    /*if (provenance!=NULL){
                        cJSON * ev = cJSON_GetObjectItem(provenance,"event");
                        cJSON * li = cJSON_GetObjectItem(provenance,"line");
                        cJSON * tr = cJSON_GetObjectItem(provenance,"trace_counter");
                        if (ev!= NULL && li != NULL && tr!= NULL){
                            char* event = ev->valuestring;
                            int line = li->valueint;
                            long trace_counter = tr->valueint;
                            pro = create_provenance_object(event,line,trace_counter);
                        }
                    }*/

                    if (!strcmp(eventName,"ch3")) {
                    char *metric;
                    double ts = 0;
                    double val = 0;
	 cJSON * fmt = cJSON_GetObjectItem(root,"params");
	 if (fmt!=NULL) {
	
metric= cJSON_GetObjectItem(fmt,"v1")->valuestring;
	ts= cJSON_GetObjectItem(fmt,"v2")->valuedouble;
	val= cJSON_GetObjectItem(fmt,"v3")->valuedouble;
	
                        ratecomputation_dataUpdate(monitor, metric, ts, val, pro);
                        printf("ratecomputation_dataUpdate called.\n");
}
	 else{
	 printf("no parameters.\n");
	}
                }
                else if (!strcmp(eventName,"ch4")) {


                        ratecomputation_timeout(monitor, pro);
                        printf("ratecomputation_timeout called.\n");
                }
                else if (!strcmp(eventName,"ch5")) {


                        ratecomputation_end(monitor, pro);
                        printf("ratecomputation_end called.\n");
                }
                }else {
                    printf("format version not matched\n");
                    
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

void send_message(RatecomputationMonitor* monitor, char* message, char* routing_key) {
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

void free_monitor(RatecomputationMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

//called at the end of each event handling function
void executeEvents(RatecomputationMonitor* monitor){
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

void executePendingEvents(RatecomputationMonitor* monitor){
    action** head = &monitor->action_queue;
    double d0, d1; char* v0;  cJSON* pro;
    while(*head!=NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type){
            case RATECOMPUTATION_DATAUPDATE2_EVENT:
            		v0 = ((params)->v);
		(params) = (params)->next;
		d0 = ((params)->d);
		(params) = (params)->next;
		d1 = ((params)->d);
		(params) = (params)->next;
pro = ((params)->provenance);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		ratecomputation_dataUpdate2(monitor, v0, d0, d1, pro);

                break;
            }
        //pop_action(head);
    }
}

//send export events one by one from export_queue
void executeExportedEvent(RatecomputationMonitor* monitor){
    action** head = &monitor->export_queue;
    double d0, d1; char* v0;  cJSON* pro;
    while(*head != NULL){
        int type = (*head)->id;
        param *params = (*head)->params;
        param *p_head = params;
        switch (type) {
            case RATECOMPUTATION_DATAUPDATE2_EVENT:
            		v0 = ((params)->v);
		(params) = (params)->next;
		d0 = ((params)->d);
		(params) = (params)->next;
		d1 = ((params)->d);
		(params) = (params)->next;
pro = ((params)->provenance);
		(params) = (params)->next;
		pop_param(&p_head);
		pop_action(head);
		exported_ratecomputation_dataUpdate2(monitor, v0, d0, d1, pro);

                break;
            }
        pop_action(head);
    }

}


/*
 * Monitor Event Handlers
 */

void ratecomputation_dataUpdate(RatecomputationMonitor* monitor, char* metric, double ts, double val, cJSON * provenance) {
if (executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]) {
    case RATECOMPUTATION_COMPUTATION_INIT:
      if(compare(metric, monitor->name)) {
        monitor->sum = val;
        monitor->curTime = ts;
        monitor->lastTime = ts;
        monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_COMPUTERATE;
      }
      else {
        raise_error("computation", ratecomputation_states_names[RATECOMPUTATION_COMPUTATION_SCENARIO][monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]], "monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]", "DEFAULT");
      }
      break;

    case RATECOMPUTATION_COMPUTATION_COMPUTERATE:
      if(compare(metric, monitor->name)) {
        monitor->sum = monitor->sum + val;
        monitor->curTime = ts;
        monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_COMPUTERATE;
      }
      else {
        raise_error("computation", ratecomputation_states_names[RATECOMPUTATION_COMPUTATION_SCENARIO][monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]], "monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]", "DEFAULT");
      }
      break;

    default:
      raise_error("ratecomputation_computation", ratecomputation_states_names[RATECOMPUTATION_COMPUTATION_SCENARIO][monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]], "dataUpdate", "DEFAULT");
      break;
  }
executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_ratecomputation_dataUpdate(RatecomputationMonitor* monitor, char* v0, double v1, double v2, cJSON* provenance) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0,NULL);
  push_param(&p_head, NULL, NULL, &v1, NULL,NULL);
  push_param(&p_head, NULL, NULL, &v2, NULL,NULL);
 push_param(&p_head, NULL, NULL, NULL, NULL,provenance);
  push_action(&monitor->action_queue, RATECOMPUTATION_DATAUPDATE_EVENT, p_head);
}


void ratecomputation_timeout(RatecomputationMonitor* monitor, cJSON * provenance) {
if (executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]) {
    case RATECOMPUTATION_COMPUTATION_INIT:
      monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_INIT;
      break;

    case RATECOMPUTATION_COMPUTATION_COMPUTERATE:
      if(monitor->curTime - monitor->lastTime > 0) {
        monitor->rate = monitor->sum / (monitor->curTime - monitor->lastTime);
        raise_ratecomputation_dataUpdate2(monitor, monitor->name, monitor->curTime, monitor->rate,provenance);
        monitor->sum = 0;
        monitor->lastTime = monitor->curTime;
        monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_COMPUTERATE;
      }
      else {
        monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_COMPUTERATE;
      }
      break;

    default:
      raise_error("ratecomputation_computation", ratecomputation_states_names[RATECOMPUTATION_COMPUTATION_SCENARIO][monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]], "timeout", "DEFAULT");
      break;
  }
executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_ratecomputation_timeout(RatecomputationMonitor* monitor, cJSON* provenance) {
  param *p_head = NULL;
 push_param(&p_head, NULL, NULL, NULL, NULL,provenance);
  push_action(&monitor->action_queue, RATECOMPUTATION_TIMEOUT_EVENT, p_head);
}


void ratecomputation_end(RatecomputationMonitor* monitor, cJSON * provenance) {
if (executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]==0) {
  switch (monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]) {
    case RATECOMPUTATION_COMPUTATION_INIT:
      monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_END;
      break;

    case RATECOMPUTATION_COMPUTATION_COMPUTERATE:
      monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO] = RATECOMPUTATION_COMPUTATION_END;
      break;

    default:
      raise_error("ratecomputation_computation", ratecomputation_states_names[RATECOMPUTATION_COMPUTATION_SCENARIO][monitor->state[RATECOMPUTATION_COMPUTATION_SCENARIO]], "end", "DEFAULT");
      break;
  }
executed_scenarios[RATECOMPUTATION_COMPUTATION_SCENARIO]=1;
  }
executeEvents(monitor);
}



void raise_ratecomputation_end(RatecomputationMonitor* monitor, cJSON* provenance) {
  param *p_head = NULL;
 push_param(&p_head, NULL, NULL, NULL, NULL,provenance);
  push_action(&monitor->action_queue, RATECOMPUTATION_END_EVENT, p_head);
}


void ratecomputation_dataUpdate2(RatecomputationMonitor* monitor, char* name, double curTime, double rate, cJSON * provenance) {
executeEvents(monitor);
}


void exported_ratecomputation_dataUpdate2(RatecomputationMonitor* monitor , char* v0, double v1, double v2, cJSON* provenance) {
  char* message;
	cJSON *root; cJSON* fmt; cJSON* prove; 
	 root = cJSON_CreateObject();
	cJSON_AddItemToObject(root, "name", cJSON_CreateString("ratecomputation_dataUpdate2"));
	cJSON_AddItemToObject(root, "fmt_version", cJSON_CreateString(msg_format_version));
	cJSON_AddItemToObject(root, "params", fmt = cJSON_CreateObject());
if (provenance!=NULL){
 cJSON_AddItemToObject(root, "provenance", prove = provenance);}
	
cJSON_AddStringToObject(fmt, "v1",v0);
cJSON_AddNumberToObject(fmt, "v2",v1);
cJSON_AddNumberToObject(fmt, "v3",v2);
message = cJSON_Print(root);

  char routing_key[256];
  sprintf(routing_key, "ch1.%ld.dataUpdate2.0.0.0", (long)(*(int*)(monitor->identities[RATECOMPUTATION_ID]->value)));
  send_message(monitor, message, routing_key);
}



void raise_ratecomputation_dataUpdate2(RatecomputationMonitor* monitor, char* v0, double v1, double v2, cJSON* provenance) {
  param *p_head = NULL;
 param *ep_head = NULL;
  push_param(&p_head, NULL, NULL, NULL, &v0,NULL);
  push_param(&ep_head, NULL, NULL, NULL, &v0,NULL);
  push_param(&p_head, NULL, NULL, &v1, NULL,NULL);
  push_param(&ep_head, NULL, NULL, &v1, NULL,NULL);
  push_param(&p_head, NULL, NULL, &v2, NULL,NULL);
  push_param(&ep_head, NULL, NULL, &v2, NULL,NULL);
 push_param(&p_head, NULL, NULL, NULL, NULL,provenance);
 push_param(&ep_head, NULL, NULL, NULL, NULL,provenance);
  push_action(&monitor->action_queue, RATECOMPUTATION_DATAUPDATE2_EVENT, p_head);
  push_action(&monitor->export_queue, RATECOMPUTATION_DATAUPDATE2_EVENT, ep_head);
}


/*
 * Monitor Utility Functions
 */

int init_ratecomputation_monitor_maps() {
    if (pthread_mutex_init(&ratecomputation_monitor_maps_lock, NULL) != 0) {
        printf("\nRatecomputation Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < RATECOMPUTATION_MONITOR_IDENTITIES; i++) {
        ratecomputation_monitor_maps[i] = (RatecomputationMonitorMap*)malloc(sizeof(RatecomputationMonitorMap));
    }
    return 1;
}

void free_ratecomputation_monitor_maps() {
    // TODO
}

int add_ratecomputation_monitor_to_map(RatecomputationMonitor *monitor, int identity) {
    RatecomputationMonitorMap* map = ratecomputation_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, RATECOMPUTATION_MONITOR_MAP_SIZE);
    RatecomputationMonitorRecord* record = (RatecomputationMonitorRecord*)malloc(sizeof(RatecomputationMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&ratecomputation_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&ratecomputation_monitor_maps_lock);
    return 1;
}

int put_ratecomputation_monitor(RatecomputationMonitor *monitor) {
    return add_ratecomputation_monitor_to_map(monitor, RATECOMPUTATION_ID);
}

RatecomputationMonitorRecord* get_ratecomputation_monitors() {
    RatecomputationMonitorRecord* results = NULL;
    RatecomputationMonitorMap* map = ratecomputation_monitor_maps[0];
    for(int i = 0; i < RATECOMPUTATION_MONITOR_MAP_SIZE; i++) {
        RatecomputationMonitorRecord* current = map->list[i];
        while(current != NULL) {
            RatecomputationMonitorRecord* record = (RatecomputationMonitorRecord*)malloc(sizeof(RatecomputationMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

RatecomputationMonitorRecord* get_ratecomputation_monitors_by_identity(int identity, int type, void *value) {
    RatecomputationMonitorRecord* results = NULL;
    RatecomputationMonitorMap* map = ratecomputation_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, RATECOMPUTATION_MONITOR_MAP_SIZE);
    RatecomputationMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            RatecomputationMonitorRecord* record = (RatecomputationMonitorRecord*)malloc(sizeof(RatecomputationMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

RatecomputationMonitorRecord* filter_ratecomputation_monitors_by_identity(RatecomputationMonitorRecord* before, int identity, void  *value) {
    RatecomputationMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            RatecomputationMonitorRecord* record = (RatecomputationMonitorRecord*)malloc(sizeof(RatecomputationMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

char* monitor_identities_str(MonitorIdentity** identities) {
    char* out = malloc(20*RATECOMPUTATION_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < RATECOMPUTATION_MONITOR_IDENTITIES; i++) {
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