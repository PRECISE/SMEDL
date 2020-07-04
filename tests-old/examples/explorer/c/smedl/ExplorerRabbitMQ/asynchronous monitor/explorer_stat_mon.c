//Compile: gcc -o explorer_stat_mon -std=c99 actions.c monitor_map.c explorer_stat_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "explorer_stat_mon.h"
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <assert.h>

#include "utils.h"
//#include <czmq.h>

typedef enum { EXPLORERSTAT_ID } explorerstat_identity;
const identity_type explorerstat_identity_types[EXPLORERSTAT_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { EXPLORERSTAT_STAT_SCENARIO, EXPLORERSTAT_CHECK_SCENARIO } explorerstat_scenario;
typedef enum { EXPLORERSTAT_STAT_START } explorerstat_stat_state;
typedef enum { EXPLORERSTAT_CHECK_CHECKSUM } explorerstat_check_state;
typedef enum { EXPLORERSTAT_RETRIEVED_EVENT, EXPLORERSTAT_REACHNUM_EVENT, EXPLORERSTAT_OUTPUT_EVENT } explorerstat_event;
typedef enum { EXPLORERSTAT_DEFAULT } explorerstat_error;
const char *explorerstat_stat_states[1] = { "Start" };
const char *explorerstat_check_states[1] = { "CheckSum" };
const char **explorerstat_states_names[2] = { explorerstat_stat_states, explorerstat_check_states };

ExplorerstatMonitor* mon1 = NULL;

char const *hostname="stability.cis.upenn.edu";
char const *username="brass";
char const *password="NeJa3EdoR";
char const *bindingkey="smedl.topic";
int port=5672;


ExplorerstatMonitor* init_explorerstat_monitor( ExplorerstatData *d ) {
    ExplorerstatMonitor* monitor = (ExplorerstatMonitor*)malloc(sizeof(ExplorerstatMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[EXPLORERSTAT_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->sum = d->sum;
    monitor->count = d->count;
    monitor->targetNum = d->targetNum;
    monitor->state[EXPLORERSTAT_STAT_SCENARIO] = EXPLORERSTAT_STAT_START;
    monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
    monitor->logFile = fopen("ExplorerstatMonitor.log", "w");
    amqp_bytes_t queuename;
    monitor->recv_conn=amqp_new_connection();
    monitor->recv_socket=amqp_tcp_socket_new(monitor->recv_conn);
    if (!monitor->recv_socket) {
        die("creating TCP socket");
    }
    
    int status = amqp_socket_open(monitor->recv_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    
    die_on_amqp_error(amqp_login(monitor->recv_conn, "/", 0, 131072, 0, AMQP_SASL_METHOD_PLAIN, username, password),
                      "Logging in");
    
    amqp_channel_open(monitor->recv_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Opening channel");
    
    {
        amqp_queue_declare_ok_t *r = amqp_queue_declare(monitor->recv_conn, 1, amqp_empty_bytes, 0, 0, 0, 1,
                                                        amqp_empty_table);
        die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Declaring queue");
        queuename = amqp_bytes_malloc_dup(r->queue);
        if (queuename.bytes == NULL) {
            fprintf(stderr, "Out of memory while copying queue name");
            return 1;
        }
    }
    
    amqp_queue_bind(monitor->recv_conn, 1, queuename, amqp_cstring_bytes("smedl.topic"), amqp_cstring_bytes(bindingkey),
                    amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");
    /*monitor->publisher = zsock_new_pub (">tcp://localhost:5559");
    assert (monitor->publisher);
    assert (zsock_resolve (monitor->publisher) != monitor->publisher);
    assert (streq (zsock_type_str (monitor->publisher), "PUB"));
    
    monitor->subscriber = zsock_new_sub (">tcp://localhost:5560","");
    assert (monitor->subscriber);
    assert (zsock_resolve (monitor->subscriber) != monitor->subscriber);
    assert (streq (zsock_type_str (monitor->subscriber), "SUB"));
    */
    monitor->send_conn = amqp_new_connection();
    monitor->send_socket = amqp_tcp_socket_new(monitor->send_conn);
    if (!monitor->send_socket) {
        die("creating TCP socket");
    }
    
    status = amqp_socket_open(monitor->send_socket, hostname, port);
    if (status) {
        die("opening TCP socket");
    }
    
    die_on_amqp_error(amqp_login(monitor->send_conn, "/", 0, 131072, 0, AMQP_SASL_METHOD_PLAIN, username, password),
                      "Logging in");
    
    amqp_channel_open(monitor->send_conn, 1);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn), "Opening channel");
    
    amqp_exchange_declare(monitor->send_conn, 1, amqp_cstring_bytes("smedl.topic"), amqp_cstring_bytes("topic"),
                          0, 0, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn), "Declaring exchange");
    put_explorerstat_monitor(monitor);
    mon1 = monitor;
    return monitor;
}

int getParameterOfRetrieved(char* eventName, char * msg){
    if(strstr(msg,eventName)==NULL){
        return -1;
    }
    if(msg != NULL){
        int position = 0;
        for(position =0;position<strlen(msg);position++){
            if(msg[position]==' '){
                break;
            }
        }
        while(position < strlen(msg)){
            if(msg[position]!=' '){
                break;
            }
            position++;
        }
        if(position != strlen(msg)){
            char intString[15] = {};
            int k = 0;
            for(int i = position;i<strlen(msg);i++){
                intString[k++] = msg[i];
            }
            intString[k]='\0';
            return atoi(intString);
        }
    }
    return -1;
}


void start_monitor(ExplorerstatMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;
    printf("begin\n");
    while(1){
        amqp_rpc_reply_t ret;
        amqp_envelope_t envelope;
        amqp_maybe_release_buffers(monitor->recv_conn);
        ret = amqp_consume_message(monitor->recv_conn, &envelope, NULL, 0);
        //if(envelope!=NULL){
            amqp_message_t msg = envelope.message;
            //if(msg!=NULL){
                amqp_bytes_t bytes = msg.body;
                //if(bytes!=NULL){
                    char* string=(char*)bytes.bytes;
                    if(string!=NULL){
                        explorerstat_retrieved(monitor,getParameterOfRetrieved("retrieved",string));
                        printf("%s\n",string);
                    }
                //}
          //  }
        //}
        //printf("ret\n");
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
                        {
                            printf("AMQP_BASIC_RETURN_METHOD\n");
                            amqp_message_t message;
                            ret = amqp_read_message(monitor->recv_conn, frame.channel, &message, 0);
                            if (AMQP_RESPONSE_NORMAL != ret.reply_type) {
                                return;
                            }
                            
                            amqp_destroy_message(&message);
                        }
                            
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

void free_monitor(ExplorerstatMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->recv_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->recv_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->recv_conn), "Ending connection");
    //zsock_destroy(&monitor->publisher);
    //zsock_destroy(&monitor->subscriber);
    
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count) {
  switch (monitor->state[EXPLORERSTAT_STAT_SCENARIO]) {
    case EXPLORERSTAT_STAT_START:
        monitor->sum = monitor->sum + 1;
        monitor->count = monitor->count + mon_var_move_count;
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: reachNum; Event parameters : "); }
      monitor->state[EXPLORERSTAT_STAT_SCENARIO] = EXPLORERSTAT_STAT_START;
         
          explorerstat_reachNum(monitor);
      break;

  }
}

void raise_explorerstat_retrieved(ExplorerstatMonitor* monitor, int mon_var_move_count) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_move_count, NULL, NULL, NULL);
  push_action(&monitor->action_queue, EXPLORERSTAT_RETRIEVED_EVENT, p_head);
}


void explorerstat_reachNum(ExplorerstatMonitor* monitor) {
   // printf("monitor->targetNum %d\n",monitor->targetNum);
  switch (monitor->state[EXPLORERSTAT_CHECK_SCENARIO]) {
    case EXPLORERSTAT_CHECK_CHECKSUM:
      if(monitor->sum < monitor->targetNum) {
        monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
      }
      else {
        { time_t action_time = time(NULL); fprintf(monitor->logFile, "%s    %s\n", ctime(&action_time), "ActionType: Raise; Event raised: output; Event parameters : "); }
          printf("count:%d,sum:%d\n",monitor->count,monitor->sum);
          int tempsum = monitor -> sum;
          int tempcount = monitor -> count;
        monitor->sum = 0;
        monitor->count = 0;
        monitor->state[EXPLORERSTAT_CHECK_SCENARIO] = EXPLORERSTAT_CHECK_CHECKSUM;
          raise_explorerstat_output(monitor,(tempcount+0.0)/tempsum);

      }
      break;

  }
}

void raise_explorerstat_reachNum(ExplorerstatMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, EXPLORERSTAT_REACHNUM_EVENT, p_head);
}



void raise_explorerstat_output(ExplorerstatMonitor* monitor, float mon_var_None) {
    printf("mon_var_None:%f\n",mon_var_None);
    param *p_head = NULL;
    push_param(&p_head, &mon_var_None, NULL, NULL, NULL);
    push_action(&monitor->action_queue, EXPLORERSTAT_OUTPUT_EVENT, p_head);
    
    // Export event to external monitors
    //char str[60];
    //sprintf(str, "/explorer/%d/retrieved  %d", monitor->identities[EXPLORER_ID]->value, mon_var_move_count);
    
    //zstr_send (monitor->publisher, str);
    printf("msum:%d,mcount:%d\n",monitor->sum,monitor->count);
    char message[256];
    amqp_bytes_t message_bytes;
    sprintf(message, "/explorer/1/output  %f", mon_var_None);
    
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes("smedl.topic"),
                                    amqp_cstring_bytes(bindingkey),
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                 "Publishing");

    
}


/*
 * Monitor Utility Functions
 */

int init_explorerstat_monitor_maps() {
    if (pthread_mutex_init(&explorerstat_monitor_maps_lock, NULL) != 0) {
        printf("\nExplorerstat Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < EXPLORERSTAT_MONITOR_IDENTITIES; i++) {
        explorerstat_monitor_maps[i] = (ExplorerstatMonitorMap*)malloc(sizeof(ExplorerstatMonitorMap));
    }
    return 1;
}

void free_explorerstat_monitor_maps() {
    // TODO
}

int add_explorerstat_monitor_to_map(ExplorerstatMonitor *monitor, int identity) {
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, EXPLORERSTAT_MONITOR_MAP_SIZE);
    ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&explorerstat_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&explorerstat_monitor_maps_lock);
    return 1;
}

int put_explorerstat_monitor(ExplorerstatMonitor *monitor) {
    return add_explorerstat_monitor_to_map(monitor, EXPLORERSTAT_ID);
}

ExplorerstatMonitorRecord* get_explorerstat_monitors() {
    ExplorerstatMonitorRecord* results = NULL;
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[0];
    for(int i = 0; i < EXPLORERSTAT_MONITOR_MAP_SIZE; i++) {
        ExplorerstatMonitorRecord* current = map->list[i];
        while(current != NULL) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

ExplorerstatMonitorRecord* get_explorerstat_monitors_by_identity(int identity, int type, void *value) {
    ExplorerstatMonitorRecord* results = NULL;
    ExplorerstatMonitorMap* map = explorerstat_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, EXPLORERSTAT_MONITOR_MAP_SIZE);
    ExplorerstatMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

ExplorerstatMonitorRecord* filter_explorerstat_monitors_by_identity(ExplorerstatMonitorRecord* before, int identity, void  *value) {
    ExplorerstatMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            ExplorerstatMonitorRecord* record = (ExplorerstatMonitorRecord*)malloc(sizeof(ExplorerstatMonitorRecord));
            record->monitor = before->monitor;
            record->next = results;
            results = record;
        }
        before = before->next;
    }
    return results;
}

void raise_error(char *scen, const char *state, char *action, char *type) {
  printf("{\"scenario\":\"%s\", \"state\":\"%s\", \"action\":\"%s\", \"type\":\"%s\"}\n", scen, state, action, type);
}
