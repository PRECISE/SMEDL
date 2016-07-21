//Compile: gcc -o {{base_file_name}}_mon -std=c99 actions.c monitor_map.c {{base_file_name}}_mon.c

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
#include "{{ base_file_name }}_mon.h"
{%- if helper %}{{ '\n' }}#include "{{ helper }}"{% endif %}

typedef enum { {{ identities_names|join(', ') }} } {{ obj|lower }}_identity;
const identity_type {{ obj|lower }}_identity_types[{{ obj|upper }}_MONITOR_IDENTITIES] = { {{ identities_types|join(', ') }} };

typedef enum { {{ scenario_names|join(', ') }} } {{ obj|lower }}_scenario;
{{ state_enums }}
typedef enum { {{ event_enums }} } {{ obj|lower }}_event;
typedef enum { {{ error_enums }} } {{ obj|lower }}_error;
{{ state_names }}
const char **{{ obj|lower }}_states_names[{{ state_names_array|length }}] = { {{ state_names_array|join(', ') }} };

#define bindingkeyNum {{ bindingkeys_num }}
const char *bindingkeys[bindingkeyNum] = { {{ bindingkeys_str }} };

{{ obj|title }}Monitor* init_{{ obj|lower }}_monitor( {{ obj|title }}Data *d ) {
    {{ obj|title }}Monitor* monitor = ({{ obj|title }}Monitor*)malloc(sizeof({{ obj|title }}Monitor));
    pthread_mutex_init(&monitor->monitor_lock, NULL);
{% for id in identities %}    monitor->identities[{{ obj|upper }}_{{ id.name|upper }}] = init_monitor_identity({{ id.type|upper }}, {% if id.type|upper == "INT" %}&{% endif -%}d->{{ id.name }});
{% endfor -%}
{% for v in state_vars %}    monitor->{{ v.name }} = d->{{ v.name }};
{% endfor %}{{state_inits}}

    /* Read settings from config file */
    config_t cfg;
    config_setting_t *setting;
    config_init(&cfg);
    if(! config_read_file(&cfg, "{{ base_file_name }}_mon.cfg"))
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

    //binding several binding keys
    for(int i = 0;i<bindingkeyNum;i++){
        amqp_queue_bind(monitor->recv_conn, 1, queuename,
            amqp_cstring_bytes(monitor->amqp_exchange), amqp_cstring_bytes(bindingkeys[i]),
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
    amqp_exchange_declare(monitor->send_conn, 1, amqp_cstring_bytes(monitor->amqp_exchange),
        amqp_cstring_bytes("topic"), 0, 0, 0, 0, amqp_empty_table);
    die_on_amqp_error(amqp_get_rpc_reply(monitor->send_conn), "Declaring exchange");

    put_{{ obj|lower }}_monitor(monitor);
    return monitor;
}

// mallocs a string for the event name
char *getEventName(char *string, size_t len){
    char *eventName = calloc(len, sizeof(char));
    for (int i; i<len && string[i]!=' '; i++) {
        eventName[i] = string[i];
    }
    return eventName;
}

void start_monitor({{ obj|title }}Monitor* monitor) {
    int received = 0;
    amqp_frame_t frame;
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

                {{ event_msg_handlers|join('\n') }}

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

void send_message({{ obj|title }}Monitor* monitor, char* message, char* routing_key) {
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

void free_monitor({{ obj|title }}Monitor* monitor) {
    die_on_amqp_error(amqp_channel_close(monitor->send_conn, 1, AMQP_REPLY_SUCCESS), "Closing channel");
    die_on_amqp_error(amqp_connection_close(monitor->send_conn, AMQP_REPLY_SUCCESS), "Closing connection");
    die_on_error(amqp_destroy_connection(monitor->send_conn), "Ending connection");
    free(monitor);
}

/*
 * Monitor Event Handlers
 */

{% for e in event_code -%}
{{ e.event|join('\n') }}
{% if e.probe %}{{ '\n' }}{{ e.probe|join('\n') }}{{ '\n' }}{% endif %}
{{ e.raise|join('\n') }}
{% endfor -%}


/*
 * Monitor Utility Functions
 */

int init_{{ obj|lower }}_monitor_maps() {
    if (pthread_mutex_init(&{{ obj|lower }}_monitor_maps_lock, NULL) != 0) {
        printf("\n{{ obj|title }} Monitor map mutex init failed\n");
        return 0;
    }
    for(int i = 0; i < {{ obj|upper }}_MONITOR_IDENTITIES; i++) {
        {{ obj|lower }}_monitor_maps[i] = ({{ obj|title }}MonitorMap*)malloc(sizeof({{ obj|title }}MonitorMap));
    }
    return 1;
}

void free_{{ obj|lower }}_monitor_maps() {
    // TODO
}

int add_{{ obj|lower }}_monitor_to_map({{ obj|title }}Monitor *monitor, int identity) {
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity];
    int bucket = hash_monitor_identity(monitor->identities[identity]->type,
        monitor->identities[identity]->value, {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
    if(monitor == NULL || record == NULL) {
        free(monitor);
        free(record);
        return 0;
    }
    record->monitor = monitor;
    pthread_mutex_lock(&{{ obj|lower }}_monitor_maps_lock);
    record->next = map->list[bucket];
    map->list[bucket] = record;
    pthread_mutex_unlock(&{{ obj|lower }}_monitor_maps_lock);
    return 1;
}

int put_{{ obj|lower }}_monitor({{ obj|title }}Monitor *monitor) {
    return {{ add_to_map_calls|join(' &&\n      ') }};
}

{{ obj|title }}MonitorRecord* get_{{ obj|lower }}_monitors() {
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[0];
    for(int i = 0; i < {{ obj|upper }}_MONITOR_MAP_SIZE; i++) {
        {{ obj|title }}MonitorRecord* current = map->list[i];
        while(current != NULL) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
            current = current->next;
        }
    }
    return results;
}

{{ obj|title }}MonitorRecord* get_{{obj|lower}}_monitors_by_identity(int identity, int type, void *value) {
    {{ obj|title }}MonitorRecord* results = NULL;
    {{ obj|title }}MonitorMap* map = {{ obj|lower }}_monitor_maps[identity];
    int bucket = hash_monitor_identity(type, value, {{ obj|upper }}_MONITOR_MAP_SIZE);
    {{ obj|title }}MonitorRecord* current = map->list[bucket];
    while(current != NULL) {
        if(compare_monitor_identity(value, current->monitor->identities[identity])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
            record->monitor = current->monitor;
            record->next = results;
            results = record;
        }
        current = current->next;
    }
    return results;
}

{{ obj|title }}MonitorRecord* filter_{{ obj|lower }}_monitors_by_identity({{ obj|title }}MonitorRecord* before, int identity, void  *value) {
    {{ obj|title }}MonitorRecord* results = NULL;
    while(before != NULL) {
        if(compare_monitor_identity(value, before->monitor->identities[identity])) {
            {{ obj|title }}MonitorRecord* record = ({{ obj|title }}MonitorRecord*)malloc(sizeof({{ obj|title }}MonitorRecord));
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

