#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "mon_utils.h"
#include "amqp_utils.h"
#include "cJSON.h"
#include "actions.h"
#include "monitor_map.h"
#include "{{ sync_set_name }}_global_wrapper.h"
{% for m in sync_set_monitors -%}
#include "{{ m }}_mon.h"
#include "{{ m }}_monitor_wrapper.h"
{% endfor -%}

// Stores all pending exported events until they can be dispatched.
global_action *sync_queue = NULL;
global_action *async_queue = NULL;

// Global RabbitMQ state that's used in both main() and send_message()
const char *amqp_exchange;
amqp_connection_state_t send_conn;

//CHANGE This function is entirely new. It's a giant nested switch that can be generated from the
// architecture file. Only exported events are present
void export_event(int monitor_type, MonitorIdentity *identities[], int event_id, param *params)
{
#ifdef DEBUG
    printf("{{ sync_set_name }} set queueing exported event: Monitor type %d, Event ID %d\n", monitor_type, event_id);
#endif //DEBUG
    
    switch (monitor_type) {
        {% for m in exported_event_routes -%}
        case {{ m.casename }}
            switch (event_id) {
                {% for e in m.events -%}
                case {{ e.casename }}
                    {{ e.callstring }}
                    break;
                {% endfor -%}
            }
            break;
        {% endfor -%}
    }
}

void send_message(char* message, char* routing_key) {
#ifdef DEBUG
    printf("{{ sync_set_name }} set sending message: %s\nbody: %s\n", routing_key, message);
#endif //DEBUG
    
    amqp_bytes_t message_bytes;
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    amqp_bytes_t routingkey_bytes;
    routingkey_bytes.len = strlen(routing_key)+1;
    routingkey_bytes.bytes = routing_key;
    die_on_error(amqp_basic_publish(send_conn,
                                    1,
                                    amqp_cstring_bytes(amqp_exchange),
                                    routingkey_bytes,
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                 "Publishing");
}

char** divideRoutingkey(char * rk, int argNum) {
    //c99 allows variable array length
    char** str = (char**)malloc(sizeof(char*)*argNum);
    int i = 0;
    char * copy[sizeof(strlen(rk))+1];
    //char * copy = (char*)malloc((sizeof(strlen(rk))+1)*sizeof(char));
    strcpy(copy, rk);
    char * temp;
    temp = strtok(copy, ".");
    for(int i = 0; i < argNum;i++){
        temp = strtok(NULL, ".");
        //if(i!=0){
        str[i] = (char*)malloc((sizeof(strlen(temp))+1)*sizeof(char));
        strcpy(str[i],temp);
        //}
    }
    return str;
}

smedl_provenance_t* create_provenance_object(char event[255], int line, long trace_counter){
    smedl_provenance_t* provenance = (smedl_provenance_t*)malloc(sizeof(smedl_provenance_t));
    strncpy(provenance -> event, event,255);
    provenance -> line = line;
    provenance -> trace_counter = trace_counter;
    return provenance;
}

param * get_param_by_idx(param * head, int idx) {
    for (int i = 0; i < idx; i++) {
        head = head->next;
    }

    return head;
}

int main() {
    //CHANGE Initialize all monitor types
    printf("Initializing monitors in {{ sync_set_name }} set...\n");
    {% for m in sync_set_monitors -%}
    init_{{ m|lower }}_monitor_maps();
    {% endfor -%}

//******************************RabbitMQ initialization *******************************************************
    
    const char *ctrl_exchange;
    amqp_socket_t *recv_socket;
    amqp_connection_state_t recv_conn;
    amqp_socket_t *send_socket;


     /* Read settings from config file */ 
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(! config_read_file(&cfg, "{{ sync_set_name|lower}}_mon.cfg"))
    {
        fprintf(stderr, "%s:%d - %s\n", config_error_file(&cfg),
            config_error_line(&cfg), config_error_text(&cfg));
        config_destroy(&cfg);
        exit(EXIT_FAILURE);
    }
    setting = config_lookup(&cfg, "rabbitmq");

    const char *hostname, *username, *password;
    int port;

    if (setting != NULL) {
        config_setting_lookup_string(setting, "hostname", &hostname);
        config_setting_lookup_int(setting, "port", &port);
        config_setting_lookup_string(setting, "username", &username);
        config_setting_lookup_string(setting, "password", &password);
        config_setting_lookup_string(setting, "exchange", &(amqp_exchange));
        config_setting_lookup_string(setting, "ctrl_exchange", &(ctrl_exchange));
    }
    /* RabbitMQ initialization */
    amqp_bytes_t queuename;
    recv_conn = amqp_new_connection();
    recv_socket = amqp_tcp_socket_new(recv_conn);
    if (!recv_socket) {
        die("creating TCP socket");
    }
    int status = amqp_socket_open(recv_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    die_on_amqp_error(amqp_login(recv_conn, "/", 0, 131072, 0,
        AMQP_SASL_METHOD_PLAIN, username, password), "Logging in");
    amqp_channel_open(recv_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Opening channel");
    amqp_queue_declare_ok_t *r = amqp_queue_declare(recv_conn, 1,
        amqp_empty_bytes, 0, 0, 0, 1, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Declaring queue");
    queuename = amqp_bytes_malloc_dup(r->queue);
    if (queuename.bytes == NULL) {
        fprintf(stderr, "Out of memory while copying queue name");
        exit(EXIT_FAILURE);
    }

    send_conn = amqp_new_connection();
    send_socket = amqp_tcp_socket_new(send_conn);
    if (!send_socket) {
        die("creating TCP socket");
    }
    status = amqp_socket_open(send_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    die_on_amqp_error(amqp_login(send_conn, "/", 0, 131072, 0,
        AMQP_SASL_METHOD_PLAIN, username, password), "Logging in");
    amqp_channel_open(send_conn, 1);

    die_on_amqp_error(amqp_get_rpc_reply(send_conn),
        "Opening channel");
    amqp_exchange_declare(send_conn, 1,
        amqp_cstring_bytes(amqp_exchange),
        amqp_cstring_bytes("topic"), 0, 1, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(send_conn),
        "Declaring primary exchange");
    amqp_exchange_declare(send_conn, 1,
        amqp_cstring_bytes(ctrl_exchange),
        amqp_cstring_bytes("fanout"), 0, 1, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(send_conn),
        "Declaring control exchange");

    //CHANGE Only need to receive for channels that come from outside the synchronous set
    // binding several binding keys
    char ** bindingkeys = (char**)malloc(bindingkeyNum*sizeof(char*));
    {% for b in b_keys -%}
    bindingkeys[{{ loop.index0 }}]=(char*)malloc(255*sizeof(char));
	strcpy(bindingkeys[{{ loop.index0 }}],"{{ b }}");
    strcat(bindingkeys[{{ loop.index0 }}],".#");
    {% endfor -%}

    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(recv_conn, 1, queuename,
            amqp_cstring_bytes(amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Binding queue");
    amqp_basic_consume(recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Consuming");

    {% for m in monitors_to_statically_init -%}
    init_default_{{ m|lower }}_monitor();
    {% endfor -%}


//*************************************************************************************************************

   // char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(50);
    sprintf(ann, "Synchronous set {{ sync_set_name }} (%s) started.", "common");
    //free(ids);
    die_on_error(amqp_basic_publish(send_conn,
                                     1,
                                     amqp_cstring_bytes(ctrl_exchange),
                                     amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                     0,
                                     0,
                                     NULL,
                                     amqp_cstring_bytes(ann)),
                   "Publishing Synchronous set {{ sync_set_name }} startup announcement");
    free(ann);

    int received = 0;

#ifdef DEBUG
    printf("{{ sync_set_name }} set starting RabbitMQ loop\n\n========================\n");
#endif //DEBUG

    while (1) 
    {
        amqp_frame_t frame;
        amqp_rpc_reply_t ret;
        amqp_envelope_t envelope;
        amqp_maybe_release_buffers(recv_conn);
        ret = amqp_consume_message(recv_conn, &envelope, NULL, 0);
        amqp_message_t msg = envelope.message;
        amqp_bytes_t bytes = msg.body;
        amqp_bytes_t routing_key = envelope.routing_key;
        char* rk = (char*)routing_key.bytes;
        //**************Added by Karan *********************************
        //int id=-1;
        //char temp[255];
        //sscanf(rk,"%s %d",temp,&id);
        //strcpy(rk,temp);
        //********************************************************
        char* string = (char*)bytes.bytes;
        //char* event[255] = {NULL};

#ifdef DEBUG
        printf("\n{{ sync_set_name }} set new message: %s\nBody: %s\n", rk, string);        
#endif //DEBUG
        
        int object_index = 0;

        if (string != NULL) {
            //char * copy = (char*)malloc((sizeof(strlen(rk))+1)*sizeof(char));
            char * copy[sizeof(strlen(rk))+1];
            strcpy(copy, rk);
            char* eventName = strtok(copy, ".");//eventName is channel name
            if (eventName != NULL) {
                cJSON * root = cJSON_Parse(string);
                cJSON * ver = cJSON_GetObjectItem(root,"fmt_version");
                char * msg_ver = NULL;
                if(ver!=NULL){
                    msg_ver = ver->valuestring;
                }
                cJSON* pro = NULL;
                if(msg_ver != NULL && !strcmp(msg_ver,msg_format_version)){
                    pro = cJSON_GetObjectItem(root,"provenance");
                    
                    //$$$$$$$$$$$$$$$$$$$$$$$$$$$
                    //CHANGE Use channel name to:
                    //  1. Identify parameter types and parse JSON
                    //  2. Send event to the correct local wrapper
                    // The parsing is from main() in the old local wrapper
                    // Note that we only need to have code for channels that originate outside the synchronous set

                    {{ event_msg_handlers }}

                } else {
                    printf("format version not matched\n");
                }
            }

        }



        if (AMQP_RESPONSE_NORMAL != ret.reply_type) {
            if (AMQP_RESPONSE_LIBRARY_EXCEPTION == ret.reply_type &&
                    AMQP_STATUS_UNEXPECTED_STATE == ret.library_error) {
                if (AMQP_STATUS_OK != amqp_simple_wait_frame(recv_conn, &frame)) {
                    return 1;
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
                            ret = amqp_read_message(recv_conn, frame.channel, &message, 0);
                            if (AMQP_RESPONSE_NORMAL != ret.reply_type) {
                                return 1;
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
                            return 1;

                        case AMQP_CONNECTION_CLOSE_METHOD:
                            /* a connection.close method happens when a connection exception occurs,
                             * this can happen by trying to use a channel that isn't open for example.
                             *
                             * In this case the whole connection must be restarted.
                             */
                            return 1;

                        default:
                            fprintf(stderr ,"An unexpected method was received %u\n", frame.payload.method.id);
                            return 1;
                    }
                }
            }
        } 
        else {
            amqp_destroy_envelope(&envelope);
        }
        received++;

#ifdef DEBUG
        printf("\n{{ sync_set_name }} set handling sync queue\n");
#endif //DEBUG
        if (sync_queue == NULL) {
#ifdef DEBUG
            printf("{{ sync_set_name }} set sync queue was empty\n");
#endif //DEBUG
        }

        //Handle the events in the sync_queue (Call local wrapper API)
        while (sync_queue != NULL) {
            // Get the event from the queue
            int monitor_type = sync_queue->monitor_type;
            MonitorIdentity **identities = sync_queue->identities;
            int event_id = sync_queue->id;
            param *params = sync_queue->params;
            
            // Route to the correct local wrapper based on monitor type and event ID
            // CHANGE Only events destined for the synchronous set need be here
            switch (monitor_type) {
                {% for m in sync_queue_handlers -%}
                case {{ sync_set_name|upper }}_{{ m.monitor_name|upper }}_MONITOR:
                    switch (event_id) {
                        {% for e in m.event_list -%}
                        case {{ m.monitor_name|upper }}_{{ e.event_name|upper }}_EVENT:
                            {{ e.callstring }}

                            pop_param(&params);
                            break;
                        {% endfor -%}
                    }
                    break;
                {% endfor -%}
            }
            
            pop_global_action(&sync_queue);
        }
        
#ifdef DEBUG
        printf("\n{{ sync_set_name }} set handling async queue\n");
#endif //DEBUG
        if (async_queue == NULL) {
#ifdef DEBUG
            printf("{{ sync_set_name }} set async queue was empty\n");
#endif //DEBUG
        }
        
        // Export the events in the async_queue to RabbitMQ
        while (async_queue != NULL) {
            // Get the event from the queue
            int monitor_type = async_queue->monitor_type;
            MonitorIdentity **identities = async_queue->identities;
            int event_id = async_queue->id;
            param *params = async_queue->params;
            
            // Call the appropriate local wrapper to export it to RabbitMQ
            switch (monitor_type) {
                {% for m in sync_set_monitors -%}
                case {{ sync_set_name|upper }}_{{ m|upper }}_MONITOR:
#ifdef DEBUG
                    printf("{{ sync_set_name }} set exporting {{ m }} event (id %d) to RabbitMQ\n", event_id);
#endif //DEBUG
                    export_async_event_{{ m|lower }}(identities, event_id, params);
                    break;
                {% endfor -%}
            }
        
            pop_global_action(&async_queue);
        }
        
#ifdef DEBUG
        printf("\n{{ sync_set_name }} set waiting for next imported asynchronous event\n\n========================\n");
#endif //DEBUG
    }

    return 0;
}
