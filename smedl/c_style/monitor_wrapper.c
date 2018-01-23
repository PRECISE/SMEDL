#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "mon_utils.h"
#include "cJSON.h"
#include "{{ base_file_name }}_mon.h"
#define bindingkeyNum {{ bindingkeys_num }}
//#define msg_format_version {{ msg_format_version }}
//**************This part will change depending on requirements of the monitor*****************************************************

typedef struct {{ obj|title }}Monitor_list{
    int {{ obj|title }}_id;
    int {{ obj|title }}Monitor_id;
    struct {{ obj|title }}Monitor_list *next;
}{{ obj|title }}Monitor_list;
//********************************************************************************************************************************

char** divideRoutingkey(char * rk, int argNum){
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


int main()
{
    //parameters for counting
    printf("init...\n");
    int monitor_index=0; //used to keep track of number of ExplorerStatMonitor created


    //instantiation of the monitor
    
    init_{{ obj|lower }}_monitor_maps();
    
    
    //create a new monitor instance if there is no identity for this monitor
    //implement after default initial value for state variables
    //{{ obj|title }}Data *tdata = ({{ obj|title }}Data*)malloc(sizeof({{ obj|title }}Data));
    //
    //Monitor *mon = init_{{ obj|title }}Monitor...(tdata);
    
    
//******************************RabbitMQ initialization *******************************************************
    
    const char *amqp_exchange;
    const char *ctrl_exchange;
    amqp_socket_t *recv_socket;
    amqp_connection_state_t recv_conn;
    amqp_socket_t *send_socket;
    amqp_connection_state_t send_conn;


     /* Read settings from config file */ 
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(! config_read_file(&cfg, "{{ obj|lower }}_mon.cfg"))
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

    // binding several binding keys
    char ** bindingkeys = (char**)malloc(bindingkeyNum*sizeof(char*));
    {{b_keys}}
    //bindingkeys[0]=(char*)malloc(255*sizeof(char));
    //strcpy(bindingkeys[0],"conn");
//strcat(bindingkeys[0],".#");
    //strcpy(bindingkeys[0],"#");

    
    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(recv_conn, 1, queuename,
            amqp_cstring_bytes(amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Binding queue");
    amqp_basic_consume(recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(recv_conn), "Consuming");

{{ mon_init_str|join('\n') }}

//*************************************************************************************************************
   // char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(50);
    sprintf(ann, "{{ obj|title }} monitor (%s) started.", "common");
    //free(ids);
    die_on_error(amqp_basic_publish(send_conn,
                                     1,
                                     amqp_cstring_bytes(ctrl_exchange),
                                     amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                     0,
                                     0,
                                     NULL,
                                     amqp_cstring_bytes(ann)),
                   "Publishing {{ obj|title }} monitor startup announcement");
    free(ann);

    
    while(1){

        int received = 0;

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
                        
                        {{ event_msg_handlers|join('\n') }}

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
        }

    }

    //TODO: subscribe to broker, receive retrieved event and publish output event
    /*for(int j=0;j<monitor_index;j++)
    {
        free_monitor(mon[j]);
    }*/
    
    //free(statData);
    //free(mon);
    /*{{ obj|title }}Monitor_list *temp=list;
    while(1)
    {
        if(temp->next==NULL)
        {
            free(temp);
            break;
        }
        else
        {
            list=list->next;
            free(temp);
            temp=list;
        }
    }*/
    return 0;
}
