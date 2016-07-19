//Compile: gcc -o poster_test_mon -std=c99 actions.c monitor_map.c poster_test_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "poster_test_mon.h"

typedef enum { POSTER_ID } poster_identity;
const identity_type poster_identity_types[POSTER_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { POSTER_SWAP_BINS_SCENARIO, POSTER_CHECK_RATE_SCENARIO, POSTER_HANDLE_DATA_SCENARIO } poster_scenario;
typedef enum { POSTER_SWAP_BINS_WAITING } poster_swap_bins_state;
typedef enum { POSTER_CHECK_RATE_WAITING } poster_check_rate_state;
typedef enum { POSTER_HANDLE_DATA_WAITING } poster_handle_data_state;
typedef enum { POSTER_CONSUME_INPUT_EVENT, POSTER_PRODUCE_TRACKS_EVENT, POSTER_HEARTBEAT_EVENT, POSTER_TOO_FEW_TRACKS_EVENT } poster_event;
typedef enum { POSTER_DEFAULT } poster_error;
const char *poster_swap_bins_states[1] = { "Waiting" };
const char *poster_check_rate_states[1] = { "Waiting" };
const char *poster_handle_data_states[1] = { "Waiting" };
const char **poster_states_names[3] = { poster_swap_bins_states, poster_check_rate_states, poster_handle_data_states };

const char *hostname, *username, *password, *exchange;
const int port;

#define bindingkeyNum 1
const char *bindingkeys[bindingkeyNum] = { "#" };

PosterMonitor* init_poster_monitor( PosterData *d ) {
    PosterMonitor* monitor = (PosterMonitor*)malloc(sizeof(PosterMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[POSTER_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->cur_tracks_out = d->cur_tracks_out;
    monitor->cur_bytes_in = d->cur_bytes_in;
    monitor->last_tracks_out = d->last_tracks_out;
    monitor->last_bytes_in = d->last_bytes_in;
    monitor->cur_time = d->cur_time;
    monitor->last_init = d->last_init;
    monitor->state[POSTER_SWAP_BINS_SCENARIO] = POSTER_SWAP_BINS_WAITING;
    monitor->state[POSTER_CHECK_RATE_SCENARIO] = POSTER_CHECK_RATE_WAITING;
    monitor->state[POSTER_HANDLE_DATA_SCENARIO] = POSTER_HANDLE_DATA_WAITING;
    monitor->logFile = fopen("PosterMonitor.log", "w");

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(! config_read_file(&cfg, "poster_test_mon.cfg"))
    {
        fprintf(stderr, "%s:%d - %s\n", config_error_file(&cfg),
            config_error_line(&cfg), config_error_text(&cfg));
        config_destroy(&cfg);
        return(EXIT_FAILURE);
    }
    setting = config_lookup(&cfg, "rabbitmq");
    if (setting != NULL) {
        config_setting_lookup_string(setting, "hostname", &hostname);
        config_setting_lookup_int(setting, "port", &port);
        config_setting_lookup_string(setting, "username", &username);
        config_setting_lookup_string(setting, "password", &password);
        config_setting_lookup_string(setting, "exchange", &exchange);
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
        return 1;
    }

    //binding several binding keys
    for(int i = 0;i<bindingkeyNum;i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(exchange), amqp_cstring_bytes(bindingkeys[i]),
            amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");
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
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn), "Opening channel");
    amqp_exchange_declare(monitor->send_conn, 1, amqp_cstring_bytes(exchange),
        amqp_cstring_bytes("topic"), 0, 0, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn), "Declaring exchange");

    put_poster_monitor(monitor);
    return monitor;
}

char * getEventName(char *string){
    int index = 0;
    for (;index<strlen(string);index++) {
        if (string[index]==' ') {
            break;
        }
    }

    if (index == strlen(string)) {
        return string;
    } else if (index != 0) {
        char substr[strlen(string)];
        strncpy(substr, string, index);
        substr[index] = '\0';
        return substr;
    } else {
        return NULL;
    }
}

void start_monitor(PosterMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;
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
        char* event[255] = {NULL};
        char* eventName = NULL;

        if (string != NULL) {
            eventName = getEventName(string);
            if (eventName != NULL) {
                char e[255];

                if (!strcmp(eventName,"poster_consume_input")) {
                    int mon_var_nbytes = 0;
                    int ret = sscanf(string, "%s %d", e, &mon_var_nbytes);
                    if (ret == 2) {
                        poster_consume_input(monitor, mon_var_nbytes);
                        printf("poster_consume_input called.\n");
                    }
                }
                else if (!strcmp(eventName,"poster_produce_tracks")) {
                    int mon_var_ntracks = 0;
                    int ret = sscanf(string, "%s %d", e, &mon_var_ntracks);
                    if (ret == 2) {
                        poster_produce_tracks(monitor, mon_var_ntracks);
                        printf("poster_produce_tracks called.\n");
                    }
                }
                else if (!strcmp(eventName,"poster_heartbeat")) {
                    int mon_var_now = 0;
                    int ret = sscanf(string, "%s %d", e, &mon_var_now);
                    if (ret == 2) {
                        poster_heartbeat(monitor, mon_var_now);
                        printf("poster_heartbeat called.\n");
                    }
                }

                else {
                    printf("error_called\n");
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

void send_message(PosterMonitor* monitor, char* message, char* routing_key) {
    amqp_bytes_t message_bytes;
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(exchange),
                                    amqp_cstring_bytes(routing_key),
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                "Publishing");

}

void free_monitor(PosterMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    fclose(monitor->logFile);
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void poster_consume_input(PosterMonitor* monitor, int mon_var_nbytes) {
  switch (monitor->state[POSTER_HANDLE_DATA_SCENARIO]) {
    case POSTER_HANDLE_DATA_WAITING:
        monitor->cur_bytes_in = monitor->cur_bytes_in + mon_var_nbytes;
      monitor->state[POSTER_HANDLE_DATA_SCENARIO] = POSTER_HANDLE_DATA_WAITING;
      break;

  }
}

void raise_poster_consume_input(PosterMonitor* monitor, int mon_var_nbytes) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_nbytes, NULL, NULL, NULL);
  push_action(&monitor->action_queue, POSTER_CONSUME_INPUT_EVENT, p_head);
}


void poster_produce_tracks(PosterMonitor* monitor, int mon_var_ntracks) {
  switch (monitor->state[POSTER_HANDLE_DATA_SCENARIO]) {
    case POSTER_HANDLE_DATA_WAITING:
        monitor->cur_tracks_out = monitor->cur_tracks_out + mon_var_ntracks;
      monitor->state[POSTER_HANDLE_DATA_SCENARIO] = POSTER_HANDLE_DATA_WAITING;
      break;

  }
}

void raise_poster_produce_tracks(PosterMonitor* monitor, int mon_var_ntracks) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_ntracks, NULL, NULL, NULL);
  push_action(&monitor->action_queue, POSTER_PRODUCE_TRACKS_EVENT, p_head);
}


void poster_heartbeat(PosterMonitor* monitor, int mon_var_now) {
  switch (monitor->state[POSTER_SWAP_BINS_SCENARIO]) {
    case POSTER_SWAP_BINS_WAITING:
        monitor->last_tracks_out = monitor->cur_tracks_out;
        monitor->last_bytes_in = monitor->cur_bytes_in;
        monitor->cur_tracks_out = 0;
        monitor->cur_bytes_in = 0;
        monitor->cur_time = mon_var_now;
        monitor->last_init = 1;
      monitor->state[POSTER_SWAP_BINS_SCENARIO] = POSTER_SWAP_BINS_WAITING;
      break;

  }
  switch (monitor->state[POSTER_CHECK_RATE_SCENARIO]) {
    case POSTER_CHECK_RATE_WAITING:
      if(monitor->last_init && track_rate_low(monitor->cur_tracks_out, monitor->cur_bytes_in, monitor->last_tracks_out, last_tracks_in)) {
        raise_poster_too_few_tracks(monitor, monitor->cur_time);
        monitor->state[POSTER_CHECK_RATE_SCENARIO] = POSTER_CHECK_RATE_WAITING;
      }
      break;

  }
}

void raise_poster_heartbeat(PosterMonitor* monitor, int mon_var_now) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_now, NULL, NULL, NULL);
  push_action(&monitor->action_queue, POSTER_HEARTBEAT_EVENT, p_head);
}




void raise_poster_too_few_tracks(PosterMonitor* monitor, int mon_var_cur_time) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_cur_time, NULL, NULL, NULL);
  push_action(&monitor->action_queue, POSTER_TOO_FEW_TRACKS_EVENT, p_head);
  char message[256];
  sprintf(message, "poster_too_few_tracks %d", mon_var_cur_time);
  char routing_key[256];
  sprintf(routing_key, "poster-poster_too_few_tracks.%d", monitor->identities[POSTER_ID]);
  send_message(monitor, message, routing_key);
}


/*
 * Monitor Utility Functions
 */

int init_poster_monitor_maps() {
    if (pthread_mutex_init(&poster_monitor_maps_lock, NULL) != 0) {
        printf("\nPoster Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < POSTER_MONITOR_IDENTITIES; i++) {
        poster_monitor_maps[i] = (PosterMonitorMap*)malloc(sizeof(PosterMonitorMap));
    }
    return 1;
}

void free_poster_monitor_maps() {
    // TODO
}

int add_poster_monitor_to_map(PosterMonitor *monitor, int identity) {
    PosterMonitorMap* map = poster_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, POSTER_MONITOR_MAP_SIZE);
    PosterMonitorRecord* record = (PosterMonitorRecord*)malloc(sizeof(PosterMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&poster_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&poster_monitor_maps_lock);
    return 1;
}

int put_poster_monitor(PosterMonitor *monitor) {
    return add_poster_monitor_to_map(monitor, POSTER_ID);
}

PosterMonitorRecord* get_poster_monitors() {
    PosterMonitorRecord* results = NULL;
    PosterMonitorMap* map = poster_monitor_maps[0];
    for(int i = 0; i < POSTER_MONITOR_MAP_SIZE; i++) {
        PosterMonitorRecord* current = map->list[i];
        while(current != NULL) {
            PosterMonitorRecord* record = (PosterMonitorRecord*)malloc(sizeof(PosterMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

PosterMonitorRecord* get_poster_monitors_by_identity(int identity, int type, void *value) {
    PosterMonitorRecord* results = NULL;
    PosterMonitorMap* map = poster_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, POSTER_MONITOR_MAP_SIZE);
    PosterMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            PosterMonitorRecord* record = (PosterMonitorRecord*)malloc(sizeof(PosterMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

PosterMonitorRecord* filter_poster_monitors_by_identity(PosterMonitorRecord* before, int identity, void  *value) {
    PosterMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            PosterMonitorRecord* record = (PosterMonitorRecord*)malloc(sizeof(PosterMonitorRecord));
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
