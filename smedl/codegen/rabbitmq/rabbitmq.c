#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <signal.h>

#include <amqp.h>
#include <amqp_framing.h>
#include <amqp_tcp_socket.h>

/* winsock2.h or sys/time.h is necessary to get struct timeval */
#if ((defined(_WIN32)) || (defined(__MINGW32__)) || (defined(__MINGW64__)))
#ifndef WINVER
#define WINVER 0x0502
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <winsock2.h>
#else
#include <sys/time.h>
#endif

#include "cJSON.h"
#include "smedl_types.h"
#include "{{syncset}}_manager.h"
#include "{{syncset}}_rabbitmq.h"

/* RabbitMQ state */
InitStatus init_status;
RabbitMQState rmq_state;

/* Keep a list of aux from the previous run_rabbitmq() to be freed at the next
 * run_rabbitmq() */
RabbitMQAux *auxes;

/* Add an aux to the aux list */
static void add_aux(RabbitMQAux *aux) {
    aux->next = auxes;
    auxes = aux;
}

/* Free all the auxes in the aux list */
static void free_auxes() {
    while (auxes != NULL) {
        RabbitMQAux *tmp = auxes;
        auxes = auxes->next;
        free(tmp->aux);
        free(tmp);
    }
}

/* Print a message to stderr followed by a newline. Arguments like printf. */
static void err(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    va_end(args);
    fprintf(stderr, "\n");
}

/* Print a message to stderr, followed by a colon and error message for the
 * given amqp_status_enum, followed by a newline. Arguments like vprintf. */
static void verr_amqp(amqp_status_enum status, const char *fmt, va_list args) {
    const char *err_msg;
    vfprintf(stderr, fmt, args);
    err_msg = amqp_error_string2(status);
    fprintf(stderr, ": %s\n", err_msg);
}

/* Check the returned amqp_status_enum. If AMQP_STATUS_OK, return nonzero.
 * Otherwise, print the given message (args like printf), followed by a colon
 * and the appropriate error message, then a newline, and return zero. */
static int check_status(amqp_status_enum status, const char *fmt, ...) {
    if (status == AMQP_STATUS_OK) {
        return 1;
    }
    va_list args;
    va_start(args, fmt);
    verr_amqp(status, fmt, args);
    va_end(args);
    return 0;
}


/* Check the returned amqp_rpc_reply_t. Return nonzero if successful. Otherwise,
 * print the given message (args like printf), followed by a colon and an error
 * description, followed by a newline, update init_status if the connection
 * and/or channel closed, and return zero. */
static int check_reply(amqp_rpc_reply_t reply, const char *fmt, ...) {
    if (reply.reply_type == AMQP_RESPONSE_NORMAL) {
        /* Success */
        return 1;
    }

    va_list args;
    va_start(args, fmt);
    if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION) {
        /* Error (e.g. server terminated the connection) */
        verr_amqp(reply.library_error, fmt, args);

    } else if (reply.reply_type == AMQP_RESPONSE_SERVER_EXCEPTION) {
        /* Server-side error */
        vfprintf(stderr, fmt, args);
        if (reply.reply.id == AMQP_CHANNEL_CLOSE_METHOD) {
            /* Channel error from server */
            amqp_channel_close_t *details =
                (amqp_channel_close_t *) reply.reply.decoded;
            fprintf(stderr, ": Channel error from server: %u %.*s\n",
                    details->reply_code, (int) details->reply_text.len,
                    (char *) details->reply_text.bytes);
            /* Respond */
            amqp_channel_close_ok_t close_ok;
            int status = amqp_send_method(rmq_state.conn, rmq_state.channel,
                    AMQP_CHANNEL_CLOSE_OK_METHOD, &close_ok);
            check_status(status, "Could not send channel_close_ok");
            /* Channel is closed. */
            init_status.channel = 0;

        } else if (reply.reply.id == AMQP_CONNECTION_CLOSE_METHOD) {
            /* Connection error from server */
            amqp_connection_close_t *details =
                (amqp_connection_close_t *) reply.reply.decoded;
            fprintf(stderr, ": Connection error from server: %u %.*s\n",
                    details->reply_code, (int) details->reply_text.len,
                    (char *) details->reply_text.bytes);
            /* Respond */
            amqp_connection_close_ok_t close_ok;
            int status = amqp_send_method(rmq_state.conn, 0,
                    AMQP_CONNECTION_CLOSE_OK_METHOD, &close_ok);
            check_status(status, "Could not send connection_close_ok");
            /* Connection is closed */
            init_status.channel = 0;
            init_status.conn = 0;

        } else {
            /* Other error from server */
            fprintf(stderr, ": Unknown server error 0x%08x\n", reply.reply.id);
        }

    } else {
        vfprintf(stderr, fmt, args);
        fprintf(stderr, ": Internal error (invalid reply type)\n");
    }
    va_end(args);

    return 0;
}

/******************************************************************************
 * Initialization and teardown                                                *
 ******************************************************************************/

/* Initialize RabbitMQ adapter.
 *
 * Returns nonzero on success, zero on failure. */
int init_rabbitmq(void) {
    init_status = (InitStatus) {0};
    rmq_state = (RabbitMQState) {.channel = 1, .rmq_config = {
        .hostname = "localhost",
        .port = 5672,
        .username = "guest",
        .password = "guest",
        .exchange = "smedl.{{sys.name}}",
        .vhost = "/"
    }};

    /* Read config, if present */
#if DEBUG >= 4
    err("Reading RabbitMQ config");
#endif
    if (!read_config("{{sys.name}}.cfg")) {
        return 0;
    }

    /* Initialize if reading config was successful */
#if DEBUG >= 4
    err("Initializing RabbitMQ");
#endif
    int status = init_rabbitmq_lib();

    if (!status) {
        /* Something failed. Clean up. */
        free_rabbitmq();
    }

    return status;
}

/* Clean up RabbitMQ adapter.
 *
 * Return nonzero on success, zero on error (in which case, cleanup was
 * performed as much as possible). */
int free_rabbitmq(void) {
    /* Use init_status to determine what needs to be cleaned up. */
    int status, result = 1;
    amqp_rpc_reply_t reply;

    /* Free queue name memory */
    if (init_status.queue) {
        amqp_bytes_free(rmq_state.queue);
    }

    /* Close channel */
    if (init_status.channel) {
        reply = amqp_channel_close(rmq_state.conn, rmq_state.channel,
                AMQP_REPLY_SUCCESS);
        if (!check_reply(reply, "Could not close channel")) {
            result = 0;
        }
    }

    /* Close the connection */
    if (init_status.conn) {
        reply = amqp_connection_close(rmq_state.conn, AMQP_REPLY_SUCCESS);
        if (!check_reply(reply, "Could not close connection")) {
            result = 0;
        }
    }

    /* Destroy the connection */
    if (init_status.conn_new) {
        status = amqp_destroy_connection(rmq_state.conn);
        if (!check_status(status, "Could not destroy connection")) {
            result = 0;
        }
    }

    /* Free config vars */
    if (init_status.config) {
        free(rmq_state.rmq_config.hostname);
        free(rmq_state.rmq_config.username);
        free(rmq_state.rmq_config.password);
        free(rmq_state.rmq_config.exchange);
        free(rmq_state.rmq_config.vhost);
    }

    return result;
}

/* Read a string configuration item into the char pointer, if the item is in
 * the parsed configuration */
static int read_config_string(cJSON *conf, const char *name, char **dest) {
    cJSON *item;
    const char *val;

    /* Try and look up item */
    item = cJSON_GetObjectItemCaseSensitive(conf, name);
    if (cJSON_IsString(item)) {
        val = item->valuestring;
    } else {
        val = *dest;
    }

    size_t len = strlen(val) + 1;
    if (len == 1) {
        err("Config strings cannot be empty");
        return 0;
    }
    char *new_dest = malloc(len);
    if (new_dest == NULL) {
        err("Out of memory storing config");
        return 0;
    }
    strcpy(new_dest, val);
    *dest = new_dest;

    return 1;
}

/* Read an int configuration item into the int pointer, if the item is in the
 * parsed configuration */
static int read_config_int(cJSON *conf, const char *name, int *dest) {
    cJSON *item;

    /* Try and look up item */
    item = cJSON_GetObjectItemCaseSensitive(conf, name);
    if (cJSON_IsNumber(item)) {
        /* Update the dest. */
        *dest = item->valueint;
    }

    return 1;
}

/* Open the file named "fname" in the current directory, if it exists. Strip
 * out any C++-style comments that are the first non-whitespace on their line.
 * Parse the result as JSON and update the config with any values that were
 * read.
 *
 * Return nonzero on success or if the file cannot be read, return zero
 * on failure. */
int read_config(const char *fname) {
    RabbitMQConfig *rmq_config = &rmq_state.rmq_config;
    /* Try to open */
    FILE *f = fopen(fname, "r");
    if (f == NULL) {
        err("Warning: Could not open config file %s. Using defaults.", fname);
        return 1;
    }

    /* Read the file */
    size_t size = 0;
    char *buf = NULL;
    do {
        char *new_buf = realloc(buf, size + 257);
        if (new_buf == NULL) {
            err("Out of memory reading config file");
            free(buf);
            fclose(f);
            return 0;
        }
        buf = new_buf;

        size_t chunk_size = fread(buf + size, 1, 256, f);
        size += chunk_size;

        if (ferror(f)) {
            err("Warning: Could not read config file %s. Using defaults.",
                    fname);
            free(buf);
            fclose(f);
            return 1;
        }
    } while (!feof(f));
    fclose(f);
    buf[size] = '\0';

    /* Clear any comments that are at the beginning of their line (except
     * whitespace) */
    int in_whitespace_prefix = 1;
    int in_comment = 0;
    char *end = buf + size;
    for (char *c = buf; c < end; c++) {
        switch (*c) {
            case '\n':
                in_whitespace_prefix = 1;
                in_comment = 0;
                break;
            case '\r':
            case '\t':
            case ' ':
                break;
            case '/':
                if (in_comment) {
                    *c = ' ';
                } else if (in_whitespace_prefix) {
                    if (c + 1 < end && *(c + 1) == '/') {
                        *c = ' ';
                        c++;
                        *c = ' ';
                        in_comment = 1;
                    }
                    in_whitespace_prefix = 0;
                }
                break;
            default:
                if (in_comment) {
                    *c = ' ';
                } else {
                    in_whitespace_prefix = 0;
                }
        }
    }

    /* Parse the config */
    cJSON *conf = cJSON_Parse(buf);
    free(buf);
    if (conf == NULL) {
        err("Config file %s is not well-formed", fname);
        return 0;
    }

    /* Update the config from the parsed data */
    if (!read_config_string(conf, "hostname", &rmq_config->hostname)) {
        goto fail_hostname;
    }
    if (!read_config_int(conf, "port", &rmq_config->port)) {
        goto fail_hostname;
    }
    if (!read_config_string(conf, "username", &rmq_config->username)) {
        goto fail_username;
    }
    if (!read_config_string(conf, "password", &rmq_config->password)) {
        goto fail_password;
    }
    if (!read_config_string(conf, "exchange", &rmq_config->exchange)) {
        goto fail_exchange;
    }
    if (!read_config_string(conf, "vhost", &rmq_config->vhost)) {
        goto fail_vhost;
    }

    /* Cleanup and return */
    cJSON_Delete(conf);
    init_status.config = 1;
    return 1;

fail_vhost:
    free(rmq_config->exchange);
fail_exchange:
    free(rmq_config->password);
fail_password:
    free(rmq_config->username);
fail_username:
    free(rmq_config->hostname);
fail_hostname:
    cJSON_Delete(conf);
    return 0;
}

/* Initialize RabbitMQ. Return nonzero on success, zero on failure. */
int init_rabbitmq_lib() {
    RabbitMQConfig *rmq_config = &rmq_state.rmq_config;
    int status;
    amqp_rpc_reply_t reply;
    amqp_socket_t *socket = NULL;

    /* Initialize connection */
#if DEBUG >= 4
    err("Creating RabbitMQ connection");
#endif
    rmq_state.conn = amqp_new_connection();
    if (rmq_state.conn == NULL) {
        err("Could not create connection");
        return 0;
    }

    /* Create socket */
#if DEBUG >= 4
    err("Creating RabbitMQ socket");
#endif
    socket = amqp_tcp_socket_new(rmq_state.conn);
    if (socket == NULL) {
        err("Could not create TCP socket");
        return 0;
    }
    init_status.conn_new = 1;

    /* Open socket */
#if DEBUG >= 4
    err("Opening RabbitMQ socket");
#endif
    status = amqp_socket_open(socket, rmq_config->hostname, rmq_config->port);
    if (!check_status(status, "Could not open TCP socket")) {
        return 0;
    }

    /* Login */
#if DEBUG >= 4
    err("Logging in RabbitMQ %p", rmq_state.conn);
#endif
    reply = amqp_login(rmq_state.conn, rmq_config->vhost, 0,
            AMQP_DEFAULT_FRAME_SIZE, 0, AMQP_SASL_METHOD_PLAIN,
            rmq_config->username, rmq_config->password);
    if (!check_reply(reply, "Could not log in")) {
        return 0;
    }
    init_status.conn = 1;

    /* Open channel */
#if DEBUG >= 4
    err("Opening RabbitMQ channel");
#endif
    amqp_channel_open(rmq_state.conn, rmq_state.channel);
    reply = amqp_get_rpc_reply(rmq_state.conn);
    if (!check_reply(reply, "Could not open channel")) {
        return 0;
    }
    init_status.channel = 1;

    /* Declare the exchange, ensuring it exists */
#if DEBUG >= 4
    err("Declaring RabbitMQ exchange");
#endif
    rmq_state.exchange = amqp_cstring_bytes(rmq_config->exchange);
    amqp_exchange_declare(rmq_state.conn, rmq_state.channel,
            rmq_state.exchange, amqp_cstring_bytes("topic"), 0, 0, 1, 0,
            amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state.conn);
    if (!check_reply(reply, "Could not declare exchange")) {
        return 0;
    }

    /* Create our queue */
#if DEBUG >= 4
    err("Declaring RabbitMQ queue");
#endif
    amqp_queue_declare_ok_t *q_ok = amqp_queue_declare(rmq_state.conn,
            rmq_state.channel, amqp_empty_bytes, 0, 0, 1, 1, amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state.conn);
    if (!check_reply(reply, "Could not declare queue")) {
        return 0;
    }
    rmq_state.queue = amqp_bytes_malloc_dup(q_ok->queue);
    if (rmq_state.queue.bytes == NULL) {
        err("Could not store queue name: Out of memory");
        return 0;
    }
    init_status.queue = 1;

    /* Bind our queue to routing keys starting with channel names we import */
#if DEBUG >= 4
    err("Binding RabbitMQ queue");
#endif
    {% for conn in sys.imported_channels(syncset) %}
    amqp_queue_bind(rmq_state.conn, rmq_state.channel, rmq_state.queue,
            rmq_state.exchange, amqp_cstring_bytes("{{conn.channel}}.#"),
            amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state.conn);
    if (!check_reply(reply, "Could not bind queue for {{conn.channel}}")) {
        return 0;
    }
    {% endfor %}

    /* Start consuming */
#if DEBUG >= 4
    err("Starting RabbitMQ consumption");
#endif
    amqp_basic_consume(rmq_state.conn, rmq_state.channel, rmq_state.queue,
            amqp_empty_bytes, 0, 0, 0, amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state.conn);
    if (!check_reply(reply, "Could not start consuming events")) {
        return 0;
    }
#if DEBUG >= 3
    err("RabbitMQ fully initialized");
#endif

    return 1;
}

/******************************************************************************
 * Incoming message handling                                                  *
 ******************************************************************************/

/* Give the RabbitMQ adapter a chance to process messages.
 *
 * If blocking is true, block until a SMEDL event comes, process it, then
 * return. If blocking is false, process all currently pending events and then
 * return.
 *
 * Returns nonzero on success, zero on failure. */
int run_rabbitmq(int blocking) {
    free_auxes();
    {% if pure_async %}
    while (!smedl_interrupted) {
    {% else %}
    while (1) {
    {% endif %}
        int result = consume_message(blocking);
        if (result == 0) {
            return 0;
        }
        if (blocking && result == 1) {
            return 1;
        }
        if (!blocking && result == 3) {
            return 1;
        }
    }
    return 1;
}

/* Consume and process one RabbitMQ message.
 *
 * Return 0 if there was an error.
 * Return 1 if a SMEDL message was consumed.
 * Return 2 if a non-SMEDL message was consumed.
 * Return 3 if:
 *  - In blocking mode, no message was received before the timeout.
 *  - In non-blocking mode, no message was pending.
 */
int consume_message(int blocking) {
    int status;
    amqp_rpc_reply_t reply;
    amqp_envelope_t envelope;
    /* Note: amqp.h contains a forward declaration for struct timeval */
    struct timeval timeout;
    int error = 0;

    /* Clean up a little */
    amqp_maybe_release_buffers(rmq_state.conn);

    /* Try to consume a message */
    timeout.tv_sec = blocking ? 1 : 0;
    timeout.tv_usec = 0;
    reply = amqp_consume_message(rmq_state.conn, &envelope, &timeout, 0);

    /* Check for timeout, unexpected frame, and errors */
    if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION &&
            reply.library_error == AMQP_STATUS_TIMEOUT) {
        /* Timeout. */
        return 3;
    } else if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION &&
            reply.library_error == AMQP_STATUS_UNEXPECTED_STATE) {
        /* Received some frame besides Basic.Deliver. Handle it. */
        if (!handle_other_frame()) {
            /* Error, but keep chugging along? */
            //return 0;
        }
        return 2;
    } else if (check_reply(reply, "Could not consume message")) {
        /* Message successfully received. Handle it. */
        if (!handle_message(&envelope)) {
            /* Error, but keep chugging along? */
            //return 0;
        }
        amqp_destroy_envelope(&envelope);
    } else {
        /* Other error. Exit the loop. */
        return 0;
    }

    return 1;
}

/* While waiting for a regular message, occasionally a non-Basic.Deliver frame
 * will arrive. That frame must be processed before continuing. This function
 * does that. Returns nonzero on success, zero on failure. */
int handle_other_frame(void) {
    int status;
    amqp_frame_t frame;
    struct timeval timeout = {
        .tv_sec = 0,
        .tv_usec = 0
    };

    /* Read the frame with zero timeout */
    status = amqp_simple_wait_frame_noblock(rmq_state.conn, &frame, &timeout);
    if (status == AMQP_STATUS_TIMEOUT) {
        /* A message should have been ready. Something is wrong. */
        err("Internal error: unable to retrieve frame");
        return 0;
    } else if (!check_status(status, "Could not retrieve frame")) {
        return 0;
    }
#if DEBUG >= 2
    if (frame.frame_type == AMQP_FRAME_METHOD) {
        printf("Received unexpected frame: id %u\n", frame.payload.method.id);
    }
#endif

    //TODO If using publisher confirms, those will likely end up here. Either
    // adjust this function or the main loop to handle it.

    return 1;
}

{% if sys.imported_channels(syncset) is nonempty %}
/* Verify that the format version is compatible, i.e. it is a string
 * "smedl-fmt<x>.<y>" where <x> matches the major version and <y> is greater
 * than or equal to the minor version. Return nonzero if so, zero if not. */
static int verify_fmt_version(const char *fmt) {
    int major, minor;
    int result = sscanf(fmt, "smedl-fmt%d.%d", &major, &minor);
    if (result != 2) {
        err("Bad message. 'type' property was present but not "
                "'smedl-fmt<major>.<minor>'.");
        return 0;
    }
    if (major != FMT_VERSION_MAJOR) {
        err("Incompatible format version. Expected %d.%d - %d.x",
                FMT_VERSION_MAJOR, FMT_VERSION_MINOR, FMT_VERSION_MAJOR);
        return 0;
    }
    if (minor < FMT_VERSION_MINOR) {
        err("Incompatible format version. Expected %d.%d - %d.x",
                FMT_VERSION_MAJOR, FMT_VERSION_MINOR, FMT_VERSION_MAJOR);
        return 0;
    }
    return 1;
}

/* Extract the channel name (the first "word") from the routing key and store
 * it in the provided buffer. */
static void routing_key_to_channel(amqp_bytes_t routing_key, char *buf,
        size_t len) {
    size_t i;
    char *rk = routing_key.bytes;
    len--;
    len = len > routing_key.len ? routing_key.len : len;
    for (i = 0; i < len; i++) {
        if (rk[i] == '.') {
            buf[i] = '\0';
            return;
        }
        buf[i] = rk[i];
    }
    buf[i] = '\0';
}

{% endif %}
/* Handle an incoming message by calling the proper global wrapper import
 * function. Return nonzero on success, zero on failure. */
int handle_message(amqp_envelope_t *envelope) {
    int status;
    /* ACK the message */
    status = amqp_basic_ack(rmq_state.conn, rmq_state.channel,
            envelope->delivery_tag, 0);
    if (!check_status(status, "Could not ack message %lx",
                envelope->delivery_tag)) {
        return 0;
    }

    {% if sys.imported_channels(syncset) is nonempty %}
    /* Skip redeliveries */
    if (envelope->redelivered) {
        return 1;
    }

    {% set ch_len = (sys.imported_channels(syncset)|map(attribute='channel')|
            map('length')|max) + 2 %}
    /* Get channel name using routing key
     * Max channel length is 2 greater than the longest channel name we
     * are interested in (to account for null terminator and at least one extra
     * char in case e.g. a channel is named "mychannel" and the routing key is
     * "mychannelislonger") */
    char channel[{{ch_len}}];
    routing_key_to_channel(envelope->routing_key, channel, {{ch_len}});

#if DEBUG >= 4
    err("Processing message with routing key %.*s (channel %s)",
            envelope->routing_key.len, envelope->routing_key.bytes, channel);
#endif

    /* Handle properties */
    amqp_basic_properties_t *properties = &envelope->message.properties;
    amqp_bytes_t *correlation_id = NULL;
    if (properties->_flags & AMQP_BASIC_TYPE_FLAG) {
        /* Verify format version */
        char fmt[257];
        size_t len = properties->type.len <= 256 ? properties->type.len : 256;
        memcpy(fmt, properties->type.bytes, len);
        fmt[len] = '\0';
        if (!verify_fmt_version(fmt)) {
            return 0;
        }
    }
    if (properties->_flags & AMQP_BASIC_CORRELATION_ID_FLAG) {
        correlation_id = &properties->correlation_id;
    }

    /* Parse JSON */
    cJSON *msg = cJSON_ParseWithLength(envelope->message.body.bytes,
            envelope->message.body.len);
    if (msg == NULL) {
        err("Received message with invalid JSON");
        return 0;
    }

    /* Get event parameters JSON */
    cJSON *params_json = cJSON_GetObjectItemCaseSensitive(msg, "params");
    if (!cJSON_IsArray(params_json)) {
        err("Bad message ('params' not present as an array)");
        goto fail1;
    }

    /* Get aux data JSON, render as string, and form RabbitMQAux */
    RabbitMQAux *aux = malloc(sizeof(RabbitMQAux));
    if (aux == NULL) {
        err("Could not malloc aux data");
        goto fail1;
    }
    cJSON *aux_json = cJSON_GetObjectItemCaseSensitive(msg, "aux");
    if (aux_json == NULL) {
        err("Bad message ('aux' not present)");
        goto fail2;
    }
    aux->aux = cJSON_PrintUnformatted(aux_json);
    if (aux->aux == NULL) {
        err("Could not serialize aux data");
        goto fail2;
    }
    if (correlation_id != NULL) {
        size_t correlation_id_len =
            correlation_id->len <= 256 ? correlation_id->len : 256;
        memcpy(aux->correlation_id, correlation_id->bytes, correlation_id_len);
        aux->correlation_id[correlation_id_len] = '\0';
    } else {
        aux->correlation_id[0] = '\0';
    }

    status = 1;

    {% for conn in sys.imported_channels(syncset) %}
    {% if conn.source_mon is not none %}
    /* Import {{conn.source_mon.name}}.{{conn.source_event}} */
    {% else %}
    /* Import {{conn.source_event}} (from target system) */
    {% endif %}
    {%+ if not loop.first %}} else {%+ endif -%}
    if (!strcmp(channel, "{{conn.channel}}")) {
        {% if conn.source_mon is not none %}
        /* Get monitor identities JSON and convert to SMEDLValue array */
        cJSON *id_json;
        cJSON *identities_json = cJSON_GetObjectItemCaseSensitive(msg, "identities");
        if (!cJSON_IsArray(identities_json)) {
            err("Bad message ('identities' not present as an array)");
            goto fail3;
        }
        {% if conn.source_mon is not none and conn.source_mon.params is nonempty %}
        SMEDLValue identities[{{conn.source_mon.params|length}}];
        {% for param in conn.source_mon.params %}
        {% if loop.first %}
        {% set get_next -%}
        cJSON_ArrayFirst(identities_json, id_json)
        {%- endset %}
        {% else %}
        {% set get_next -%}
        cJSON_ArrayNext(id_json)
        {%- endset %}
        {% endif %}
        {% if param is sameas SmedlType.INT %}
        if ({{get_next}} && cJSON_IsNumber(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_INT;
            identities[{{loop.index0}}].v.i = id_json->valueint;
        {% elif param is sameas SmedlType.FLOAT %}
        if ({{get_next}} && cJSON_IsNumber(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_FLOAT;
            identities[{{loop.index0}}].v.d = id_json->valuedouble;
        {% elif param is sameas SmedlType.CHAR %}
        if ({{get_next}} && cJSON_IsNumber(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_CHAR;
            identities[{{loop.index0}}].v.c = id_json->valueint;
        {% elif param is sameas SmedlType.STRING %}
        if ({{get_next}} && cJSON_IsString(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_STRING;
            identities[{{loop.index0}}].v.s = id_json->valuestring;
        {% elif param is sameas SmedlType.POINTER %}
        if ({{get_next}} && cJSON_IsString(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_POINTER;
            if (!smedl_string_to_pointer(id_json->valuestring, &identities[{{loop.index0}}].v.p)) {
                err("Could not extract pointer from 'identities': Overflow or "
                        "bad message");
                goto fail3;
            }
        {% elif param is sameas SmedlType.OPAQUE %}
        if ({{get_next}} && cJSON_IsString(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_OPAQUE;
            identities[{{loop.index0}}].v.o.data = id_json->valuestring;
            identities[{{loop.index0}}].v.o.size = strlen(id_json->valuestring);
        {% endif %}
        } else {
            err("Bad message (Bad 'identities' array)");
            goto fail3;
        }
        {% endfor %}
        if (cJSON_ArrayNext(id_json)) {
            err("Bad message (Too many elements in 'identities' array)");
            goto fail3;
        }
        {% else %}
        SMEDLValue *identities = NULL;
        if (cJSON_ArrayFirst(identities_json, id_json)) {
            err("Bad message (Too many elements in 'identities' array)");
            goto fail3;
        }
        {% endif %}
        {% else %}
        SMEDLValue *identities = NULL;
        {% endif %}

        /* Convert event parameters to SMEDLValue array */
        cJSON *param_json;
        {% if conn.source_event_params is nonempty %}
        SMEDLValue params[{{conn.source_event_params|length}}];
        {% for param in conn.source_event_params %}
        {% if loop.first %}
        {% set get_next -%}
        cJSON_ArrayFirst(params_json, param_json)
        {%- endset %}
        {% else %}
        {% set get_next -%}
        cJSON_ArrayNext(param_json)
        {%- endset %}
        {% endif %}
        {% if param is sameas SmedlType.INT %}
        if ({{get_next}} && cJSON_IsNumber(param_json)) {
            params[{{loop.index0}}].t = SMEDL_INT;
            params[{{loop.index0}}].v.i = param_json->valueint;
        {% elif param is sameas SmedlType.FLOAT %}
        if ({{get_next}} && cJSON_IsNumber(param_json)) {
            params[{{loop.index0}}].t = SMEDL_FLOAT;
            params[{{loop.index0}}].v.d = param_json->valuedouble;
        {% elif param is sameas SmedlType.CHAR %}
        if ({{get_next}} && cJSON_IsNumber(param_json)) {
            params[{{loop.index0}}].t = SMEDL_CHAR;
            params[{{loop.index0}}].v.c = param_json->valueint;
        {% elif param is sameas SmedlType.STRING %}
        if ({{get_next}} && cJSON_IsString(param_json)) {
            params[{{loop.index0}}].t = SMEDL_STRING;
            params[{{loop.index0}}].v.s = param_json->valuestring;
        {% elif param is sameas SmedlType.POINTER %}
        if ({{get_next}} && cJSON_IsString(param_json)) {
            params[{{loop.index0}}].t = SMEDL_POINTER;
            if (!smedl_string_to_pointer(param_json->valuestring, &params[{{loop.index0}}].v.p)) {
                err("Could not extract pointer from 'params': Overflow or "
                        "bad message");
                goto fail3;
            }
        {% elif param is sameas SmedlType.OPAQUE %}
        if ({{get_next}} && cJSON_IsString(param_json)) {
            params[{{loop.index0}}].t = SMEDL_OPAQUE;
            params[{{loop.index0}}].v.o.data = param_json->valuestring;
            params[{{loop.index0}}].v.o.size = strlen(param_json->valuestring);
        {% elif param is none %}
        if ({{get_next}}) {
            /* Parameter {{loop.index0}} not needed (thus type not inferred) */
            params[{{loop.index0}}].t = SMEDL_NULL;
        {% endif %}
        } else {
            err("Bad message (Bad 'params' array)");
            goto fail3;
        }
        {% endfor %}
        {% if not conn.event_params_inferred %}
        if (cJSON_ArrayNext(param_json)) {
            err("Bad message (Too many elements in 'params' array)");
            goto fail3;
        }
        {% endif %}
        {% else %}
        SMEDLValue *params = NULL;
        {% if not conn.event_params_inferred %}
        if (cJSON_ArrayFirst(params_json, param_json)) {
            err("Bad message (Too many elements in 'params' array)");
            goto fail3;
        }
        {% endif %}
        {% endif %}

        /* Send to manager */
        status = report_{{conn.mon_string}}_{{conn.source_event}}(identities, params, aux) && status;
    {% endfor %}
    }

    /* Cleanup */
    add_aux(aux);
    cJSON_Delete(msg);
    return status;

fail3:
    free(aux->aux);
fail2:
    free(aux);
fail1:
    cJSON_Delete(msg);
    return 0;
    {% else %}
    /* This syncset does not receive any incoming asynchronous events. */
    return 1;
    {% endif %}
}

/******************************************************************************
 * Outgoing message handling                                                  *
 ******************************************************************************/

/* Send a message over RabbitMQ. Return nonzero on success, zero on failure. */
int send_message(const char *routing_key, const char *correlation_id,
        const char *msg, size_t len) {
    int status;

    /* Construct RabbitMQ message */
    amqp_bytes_t routing_key_bytes, msg_bytes;
    routing_key_bytes = amqp_cstring_bytes(routing_key);
    msg_bytes.len = len;
    msg_bytes.bytes = (char *) msg;
    amqp_basic_properties_t properties;
    properties._flags = AMQP_BASIC_CONTENT_TYPE_FLAG | AMQP_BASIC_TYPE_FLAG;
    properties.content_type = amqp_cstring_bytes("application/json");
    properties.type = amqp_cstring_bytes(FMT_VERSION_STRING);
    if (correlation_id != NULL && correlation_id[0] != '\0') {
        properties._flags |= AMQP_BASIC_CORRELATION_ID_FLAG;
        properties.correlation_id = amqp_cstring_bytes(correlation_id);
    }

    /* Send the message */
    status = amqp_basic_publish(rmq_state.conn, rmq_state.channel,
            rmq_state.exchange, routing_key_bytes, 0, 0,
            &properties, msg_bytes);
    if (!check_status(status, "Could not send message")) {
        return 0;
    }

    return 1;
}

/* Event forwarding functions - Send an asynchronous event over RabbutMQ.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.exported_channels(syncset).keys() %}

int forward_rabbitmq_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux_void) {
    char ptr[40];
    char *opaque;
    int status;
    RabbitMQAux *aux = aux_void;
    /* Construct the JSON message */
    cJSON *msg_json;
    msg_json = cJSON_CreateObject();
    if (msg_json == NULL) {
        /* malloc fail */
        err("Could not create JSON object for message serialization");
        return 0;
    }

    {% if conn.source_mon is not none %}
    if (cJSON_AddStringToObject(msg_json, "event", "{{conn.source_mon.name}}.{{conn.source_event}}") == NULL) {
    {% else %}
    if (cJSON_AddStringToObject(msg_json, "event", "{{conn.source_event}}") == NULL) {
    {% endif %}
        err("Could not add event name to JSON for message serialization");
        goto fail;
    }
    {% if conn.source_mon is not none %}

    /* Add the identities */
    cJSON *ids_json = cJSON_AddArrayToObject(msg_json, "identities");
    if (ids_json == NULL) {
        err("Could not add identities array to JSON for message serialization");
        goto fail;
    }
    cJSON *id;
    {% for param in conn.source_mon.params %}
    {% if param is sameas SmedlType.INT %}
    id = cJSON_CreateNumber(identities[{{loop.index0}}].v.i);
    {% elif param is sameas SmedlType.FLOAT %}
    id = cJSON_CreateNumber(identities[{{loop.index0}}].v.d);
    {% elif param is sameas SmedlType.CHAR %}
    id = cJSON_CreateNumber(identities[{{loop.index0}}].v.c);
    {% elif param is sameas SmedlType.STRING %}
    id = cJSON_CreateString(identities[{{loop.index0}}].v.s);
    {% elif param is sameas SmedlType.POINTER %}
    if (!smedl_pointer_to_string(identities[{{loop.index0}}].v.p, ptr, sizeof(ptr))) {
        err("Could not convert pointer to string for message serialization");
        goto fail;
    }
    id = cJSON_CreateString(ptr);
    {% elif param is sameas SmedlType.OPAQUE %}
    opaque = malloc(identities[{{loop.index0}}].v.o.size + 1);
    if (opaque == NULL) {
        err("Could not convert opaque to string for message serialization");
        goto fail;
    }
    memcpy(opaque, identities[{{loop.index0}}].v.o.data, identities[{{loop.index0}}].v.o.size);
    opaque[identities[{{loop.index0}}].v.o.size] = '\0';
    id = cJSON_CreateString(opaque);
    free(opaque);
    {% endif %}
    if (id == NULL) {
        err("Could not add identity to JSON array for message serialization");
        goto fail;
    }
    cJSON_AddItemToArray(ids_json, id);
    {% endfor %}
    {% endif %}

    /* Add the event params */
    cJSON *params_json = cJSON_AddArrayToObject(msg_json, "params");
    if (params_json == NULL) {
        err("Could not add params array to JSON for message serialization");
        goto fail;
    }
    cJSON *param;
    {% for param in conn.source_event_params %}
    {% if param is sameas SmedlType.INT %}
    param = cJSON_CreateNumber(params[{{loop.index0}}].v.i);
    {% elif param is sameas SmedlType.FLOAT %}
    param = cJSON_CreateNumber(params[{{loop.index0}}].v.d);
    {% elif param is sameas SmedlType.CHAR %}
    param = cJSON_CreateNumber(params[{{loop.index0}}].v.c);
    {% elif param is sameas SmedlType.STRING %}
    param = cJSON_CreateString(params[{{loop.index0}}].v.s);
    {% elif param is sameas SmedlType.POINTER %}
    if (!smedl_pointer_to_string(params[{{loop.index0}}].v.p, ptr, sizeof(ptr))) {
        err("Could not convert pointer to string for message serialization");
        goto fail;
    }
    param = cJSON_CreateString(ptr);
    {% elif param is sameas SmedlType.OPAQUE %}
    opaque = malloc(params[{{loop.index0}}].v.o.size + 1);
    if (opaque == NULL) {
        err("Could not convert opaque to string for message serialization");
        goto fail;
    }
    memcpy(opaque, params[{{loop.index0}}].v.o.data, params[{{loop.index0}}].v.o.size);
    opaque[params[{{loop.index0}}].v.o.size] = '\0';
    param = cJSON_CreateString(opaque);
    free(opaque);
    {% endif %}
    if (param == NULL) {
        err("Could not add param to JSON array for message serialization");
        goto fail;
    }
    cJSON_AddItemToArray(params_json, param);
    {% endfor %}

    /* Add the Aux data */
    if (aux == NULL || aux->aux == NULL) {
        if (cJSON_AddNullToObject(msg_json, "aux") == NULL) {
            err("Could not add null aux data to JSON for message serialization");
            goto fail;
        }
    } else if (cJSON_AddRawToObject(msg_json, "aux", aux->aux) == NULL) {
        err("Could not add aux data to JSON for message serialization");
        goto fail;
    }

    char *msg = cJSON_Print(msg_json);
    if (msg == NULL) {
        err("Could not convert JSON to string for message serialization");
        goto fail;
    }

    char *correlation_id = NULL;
    if (aux != NULL) {
        correlation_id = aux->correlation_id;
    }
    {% if conn.source_mon is not none %}
    send_message("{{conn.channel}}.{{conn.source_mon.name}}.{{conn.source_event}}", correlation_id, msg, strlen(msg));
    {% else %}
    send_message("{{conn.channel}}.{{conn.source_event}}", correlation_id, msg, strlen(msg));
    {% endif %}

    free(msg);
    cJSON_Delete(msg_json);
    return 1;

fail:
    /* malloc or snprintf fail */
    cJSON_Delete(msg_json);
    return 0;
}
{% endfor %}
