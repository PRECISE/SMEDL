//Compile: gcc -o spv_mon -std=c99 actions.c monitor_map.c spv_mon.c

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include <stdint.h>
#include <amqp_tcp_socket.h>
#include <amqp.h>
#include <amqp_framing.h>
#include <libconfig.h>
#include "utils.h"
#include "spv_mon.h"

typedef enum { SPV_ID } spv_identity;
const identity_type spv_identity_types[SPV_MONITOR_IDENTITIES] = { OPAQUE };

typedef enum { SPV_CHECK_TIME_SCENARIO, SPV_CHECK_LATITUDE_SCENARIO, SPV_CHECK_LONGITUDE_SCENARIO, SPV_CHECK_DISTANCE_SCENARIO, SPV_AFTER_END_SCENARIO } spv_scenario;
typedef enum { SPV_CHECK_TIME_START } spv_check_time_state;
typedef enum { SPV_CHECK_LATITUDE_START } spv_check_latitude_state;
typedef enum { SPV_CHECK_LONGITUDE_START } spv_check_longitude_state;
typedef enum { SPV_CHECK_DISTANCE_START } spv_check_distance_state;
typedef enum { SPV_AFTER_END_START, SPV_AFTER_END_END } spv_after_end_state;
typedef enum { SPV_PARSE_RECORD_EVENT, SPV_TOTAL_DISTANCE_EVENT, SPV_TIMESTEP_ERROR_EVENT, SPV_AFTER_END_ERROR_EVENT, SPV_LATITUDE_RANGE_ERROR_EVENT, SPV_LONGITUDE_RANGE_ERROR_EVENT, SPV_TOTAL_DISTANCE_ERROR_EVENT } spv_event;
typedef enum { SPV_DEFAULT } spv_error;
const char *spv_check_time_states[1] = { "Start" };
const char *spv_check_latitude_states[1] = { "Start" };
const char *spv_check_longitude_states[1] = { "Start" };
const char *spv_check_distance_states[1] = { "Start" };
const char *spv_after_end_states[2] = { "Start", "End" };
const char **spv_states_names[5] = { spv_check_time_states, spv_check_latitude_states, spv_check_longitude_states, spv_check_distance_states, spv_after_end_states };

#define bindingkeyNum 1
const char *bindingkeys[bindingkeyNum] = { "#" };

SpvMonitor* init_spv_monitor( SpvData *d ) {
    SpvMonitor* monitor = (SpvMonitor*)malloc(sizeof(SpvMonitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
    monitor->identities[SPV_ID] = init_monitor_identity(OPAQUE, d->id);
    monitor->last_time = d->last_time;
    monitor->state[SPV_CHECK_TIME_SCENARIO] = SPV_CHECK_TIME_START;
    monitor->state[SPV_CHECK_LATITUDE_SCENARIO] = SPV_CHECK_LATITUDE_START;
    monitor->state[SPV_CHECK_LONGITUDE_SCENARIO] = SPV_CHECK_LONGITUDE_START;
    monitor->state[SPV_CHECK_DISTANCE_SCENARIO] = SPV_CHECK_DISTANCE_START;
    monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_START;
    monitor->action_queue = NULL;

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(! config_read_file(&cfg, "spv_mon.cfg"))
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
        config_setting_lookup_string(setting, "exchange", &(monitor->amqp_exchange));
        config_setting_lookup_string(setting, "ctrl_exchange", &(monitor->ctrl_exchange));
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
    for(int i = 0; i < bindingkeyNum; i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(monitor->amqp_exchange),
            amqp_cstring_bytes(bindingkeys[i]), amqp_empty_table);
    }

    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Binding queue");
    amqp_basic_consume(monitor->recv_conn, 1, queuename, amqp_empty_bytes, 0, 1, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->recv_conn), "Consuming");

    put_spv_monitor(monitor);
    return monitor;
}

// mallocs a string for the event name
// returns null if the given string isn't a properly-terminated c string
char *getEventName(char *str, size_t maxlen){
    // make sure that str is really a cstring before trying to copy from it.
    size_t len = strnlen(str, maxlen);
    if (len >= maxlen) {
        return NULL;
    }
    // find the first space or the end of the string
    char* end = index(str, ' ');
    // copylen is the length of the string with the terminator
    size_t copylen;
    if (NULL == end) {
      copylen = maxlen - 1;
    } else {
      copylen = end - str;
    }
    char* eventName = malloc(copylen+1);
    memcpy(eventName, str, copylen);
    eventName[copylen] = '\0';
    return eventName;
}

void start_monitor(SpvMonitor* monitor) {
    int received = 0;
    amqp_frame_t frame;

    // Announce that the monitor has started
    char* ids = monitor_identities_str(monitor->identities);
    char* ann = malloc(strlen(ids)+50);
    sprintf(ann, "Spv monitor (%s) started.", ids);
    free(ids);
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->ctrl_exchange),
                                    amqp_cstring_bytes("smedl.control"), // Ignored due to fanout exchange
                                    0,
                                    0,
                                    NULL,
                                    amqp_cstring_bytes(ann)),
                "Publishing Spv monitor startup announcement");
    free(ann);

    while (1) {
        amqp_rpc_reply_t ret;
        amqp_envelope_t envelope;
        amqp_maybe_release_buffers(monitor->recv_conn);
        ret = amqp_consume_message(monitor->recv_conn, &envelope, NULL, 0);
        amqp_message_t msg = envelope.message;
        amqp_bytes_t bytes = msg.body;
        //amqp_bytes_t routing_key = envelope.routing_key;
        //char* rk = (char*)routing_key.bytes;
        char* string = (char*)bytes.bytes;
        //char* event[255] = {NULL};

        if (string != NULL) {
            char* eventName = getEventName(string, bytes.len);
            if (eventName != NULL) {
                char e[255];

                if (!strcmp(eventName,"spv_parse_record")) {
                    int mon_var_tm = 0;
                    double mon_var_lat = 0;
                    double mon_var_lon = 0;
                    int mon_var_ret = 0;
                    int ret = sscanf(string, "%s %d %lf %lf %d", e, &mon_var_tm, &mon_var_lat, &mon_var_lon, &mon_var_ret);
                    if (ret == 5) {
                        spv_parse_record(monitor, mon_var_tm, mon_var_lat, mon_var_lon, mon_var_ret);
                        printf("spv_parse_record called.\n");
                    }
                }
                else if (!strcmp(eventName,"spv_total_distance")) {
                    double mon_var_dist = 0;
                    int ret = sscanf(string, "%s %lf", e, &mon_var_dist);
                    if (ret == 2) {
                        spv_total_distance(monitor, mon_var_dist);
                        printf("spv_total_distance called.\n");
                    }
                }

                else {
                    printf("error_called\n");
                }
            }
            free(eventName);
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

void send_message(SpvMonitor* monitor, char* message, char* routing_key) {
    amqp_bytes_t message_bytes;
    message_bytes.len = strlen(message)+1;
    message_bytes.bytes = message;
    die_on_error(amqp_basic_publish(monitor->send_conn,
                                    1,
                                    amqp_cstring_bytes(monitor->amqp_exchange),
                                    amqp_cstring_bytes(routing_key),
                                    0,
                                    0,
                                    NULL,
                                    message_bytes),
                "Publishing");

}

void free_monitor(SpvMonitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

void spv_parse_record(SpvMonitor* monitor, int mon_var_tm, double mon_var_lat, double mon_var_lon, int mon_var_ret) {
  switch (monitor->state[SPV_CHECK_TIME_SCENARIO]) {
    case SPV_CHECK_TIME_START:
      if(mon_var_ret == -1 || mon_var_tm > monitor->last_time) {
        monitor->last_time = mon_var_tm;
        monitor->state[SPV_CHECK_TIME_SCENARIO] = SPV_CHECK_TIME_START;
      }
      else {
        raise_spv_timestep_error(monitor, mon_var_tm, monitor->last_time);
        monitor->state[SPV_CHECK_TIME_SCENARIO] = SPV_CHECK_TIME_START;
      }
      break;

    default:
      raise_error("spv_check_time", spv_states_names[SPV_CHECK_TIME_SCENARIO][monitor->state[SPV_CHECK_TIME_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
  switch (monitor->state[SPV_CHECK_LATITUDE_SCENARIO]) {
    case SPV_CHECK_LATITUDE_START:
      if(mon_var_lat >= -90 && mon_var_lat <= 90) {
        monitor->state[SPV_CHECK_LATITUDE_SCENARIO] = SPV_CHECK_LATITUDE_START;
      }
      else {
        raise_spv_latitude_range_error(monitor, mon_var_lat);
        monitor->state[SPV_CHECK_LATITUDE_SCENARIO] = SPV_CHECK_LATITUDE_START;
      }
      break;

    default:
      raise_error("spv_check_latitude", spv_states_names[SPV_CHECK_LATITUDE_SCENARIO][monitor->state[SPV_CHECK_LATITUDE_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
  switch (monitor->state[SPV_CHECK_LONGITUDE_SCENARIO]) {
    case SPV_CHECK_LONGITUDE_START:
      if(mon_var_lon >= -180 && mon_var_lon <= +180) {
        monitor->state[SPV_CHECK_LONGITUDE_SCENARIO] = SPV_CHECK_LONGITUDE_START;
      }
      else {
        raise_spv_longitude_range_error(monitor, mon_var_lon);
        monitor->state[SPV_CHECK_LONGITUDE_SCENARIO] = SPV_CHECK_LONGITUDE_START;
      }
      break;

    default:
      raise_error("spv_check_longitude", spv_states_names[SPV_CHECK_LONGITUDE_SCENARIO][monitor->state[SPV_CHECK_LONGITUDE_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
  switch (monitor->state[SPV_AFTER_END_SCENARIO]) {
    case SPV_AFTER_END_END:
        raise_spv_after_end_error(monitor);
      monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_END;
      break;

    case SPV_AFTER_END_START:
      if(mon_var_ret == -1) {
        monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_END;
      }
      else {
        monitor->state[SPV_AFTER_END_SCENARIO] = SPV_AFTER_END_START;
      }
      break;

    default:
      raise_error("spv_after_end", spv_states_names[SPV_AFTER_END_SCENARIO][monitor->state[SPV_AFTER_END_SCENARIO]], "parse_record", "DEFAULT");
      break;
  }
}

void raise_spv_parse_record(SpvMonitor* monitor, int mon_var_tm, double mon_var_lat, double mon_var_lon, int mon_var_ret) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_tm, NULL, NULL, NULL);
  push_param(&p_head, NULL, NULL, &mon_var_lat, NULL);
  push_param(&p_head, NULL, NULL, &mon_var_lon, NULL);
  push_param(&p_head, &mon_var_ret, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SPV_PARSE_RECORD_EVENT, p_head);
}


void spv_total_distance(SpvMonitor* monitor, double mon_var_dist) {
  switch (monitor->state[SPV_CHECK_DISTANCE_SCENARIO]) {
    case SPV_CHECK_DISTANCE_START:
      if(mon_var_dist > 0 && mon_var_dist < 1) {
        monitor->state[SPV_CHECK_DISTANCE_SCENARIO] = SPV_CHECK_DISTANCE_START;
      }
      else {
        raise_spv_total_distance_error(monitor, mon_var_dist);
        monitor->state[SPV_CHECK_DISTANCE_SCENARIO] = SPV_CHECK_DISTANCE_START;
      }
      break;

    default:
      raise_error("spv_check_distance", spv_states_names[SPV_CHECK_DISTANCE_SCENARIO][monitor->state[SPV_CHECK_DISTANCE_SCENARIO]], "total_distance", "DEFAULT");
      break;
  }
}

void raise_spv_total_distance(SpvMonitor* monitor, double mon_var_dist) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, &mon_var_dist, NULL);
  push_action(&monitor->action_queue, SPV_TOTAL_DISTANCE_EVENT, p_head);
}




void raise_spv_timestep_error(SpvMonitor* monitor, int mon_var_tm, int mon_var_last_time) {
  param *p_head = NULL;
  push_param(&p_head, &mon_var_tm, NULL, NULL, NULL);
  push_param(&p_head, &mon_var_last_time, NULL, NULL, NULL);
  push_action(&monitor->action_queue, SPV_TIMESTEP_ERROR_EVENT, p_head);
  char message[256];
  sprintf(message, "spv_timestep_error %d %d", mon_var_tm, mon_var_last_time);
  char routing_key[256];
  sprintf(routing_key, "spv-spv_timestep_error.%ld", (long)monitor->identities[SPV_ID]);
  send_message(monitor, message, routing_key);
}




void raise_spv_after_end_error(SpvMonitor* monitor) {
  param *p_head = NULL;
  push_action(&monitor->action_queue, SPV_AFTER_END_ERROR_EVENT, p_head);
  char message[256];
  sprintf(message, "spv_after_end_error");
  char routing_key[256];
  sprintf(routing_key, "spv-spv_after_end_error.%ld", (long)monitor->identities[SPV_ID]);
  send_message(monitor, message, routing_key);
}




void raise_spv_latitude_range_error(SpvMonitor* monitor, double mon_var_lat) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, &mon_var_lat, NULL);
  push_action(&monitor->action_queue, SPV_LATITUDE_RANGE_ERROR_EVENT, p_head);
  char message[256];
  sprintf(message, "spv_latitude_range_error %lf", mon_var_lat);
  char routing_key[256];
  sprintf(routing_key, "spv-spv_latitude_range_error.%ld", (long)monitor->identities[SPV_ID]);
  send_message(monitor, message, routing_key);
}




void raise_spv_longitude_range_error(SpvMonitor* monitor, double mon_var_lon) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, &mon_var_lon, NULL);
  push_action(&monitor->action_queue, SPV_LONGITUDE_RANGE_ERROR_EVENT, p_head);
  char message[256];
  sprintf(message, "spv_longitude_range_error %lf", mon_var_lon);
  char routing_key[256];
  sprintf(routing_key, "spv-spv_longitude_range_error.%ld", (long)monitor->identities[SPV_ID]);
  send_message(monitor, message, routing_key);
}




void raise_spv_total_distance_error(SpvMonitor* monitor, double mon_var_dist) {
  param *p_head = NULL;
  push_param(&p_head, NULL, NULL, &mon_var_dist, NULL);
  push_action(&monitor->action_queue, SPV_TOTAL_DISTANCE_ERROR_EVENT, p_head);
  char message[256];
  sprintf(message, "spv_total_distance_error %lf", mon_var_dist);
  char routing_key[256];
  sprintf(routing_key, "spv-spv_total_distance_error.%ld", (long)monitor->identities[SPV_ID]);
  send_message(monitor, message, routing_key);
}


/*
 * Monitor Utility Functions
 */

int init_spv_monitor_maps() {
    if (pthread_mutex_init(&spv_monitor_maps_lock, NULL) != 0) {
        printf("\nSpv Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < SPV_MONITOR_IDENTITIES; i++) {
        spv_monitor_maps[i] = (SpvMonitorMap*)malloc(sizeof(SpvMonitorMap));
    }
    return 1;
}

void free_spv_monitor_maps() {
    // TODO
}

int add_spv_monitor_to_map(SpvMonitor *monitor, int identity) {
    SpvMonitorMap* map = spv_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, SPV_MONITOR_MAP_SIZE);
    SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&spv_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&spv_monitor_maps_lock);
    return 1;
}

int put_spv_monitor(SpvMonitor *monitor) {
    return add_spv_monitor_to_map(monitor, SPV_ID);
}

SpvMonitorRecord* get_spv_monitors() {
    SpvMonitorRecord* results = NULL;
    SpvMonitorMap* map = spv_monitor_maps[0];
    for(int i = 0; i < SPV_MONITOR_MAP_SIZE; i++) {
        SpvMonitorRecord* current = map->list[i];
        while(current != NULL) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

SpvMonitorRecord* get_spv_monitors_by_identity(int identity, int type, void *value) {
    SpvMonitorRecord* results = NULL;
    SpvMonitorMap* map = spv_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, SPV_MONITOR_MAP_SIZE);
    SpvMonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

SpvMonitorRecord* filter_spv_monitors_by_identity(SpvMonitorRecord* before, int identity, void  *value) {
    SpvMonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            SpvMonitorRecord* record = (SpvMonitorRecord*)malloc(sizeof(SpvMonitorRecord));
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

char* monitor_identities_str(MonitorIdentity** identities) {
    char* out = malloc(20*SPV_MONITOR_IDENTITIES);
    out[0] = '\0';
    for(int i = 0; i < SPV_MONITOR_IDENTITIES; i++) {
        char* new_str;
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