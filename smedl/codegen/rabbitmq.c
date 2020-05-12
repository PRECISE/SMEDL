/*
 * RabbitMQ Adapter
 *
 * RabbitMQ messages are published to exchanges. RabbitMQ subscribers read from
 * queues. Queues can be bound to exchanges, which allows the exchange to route
 * messages into it. How that routing happens depends on the exchange type.
 *
 * SMEDL uses the "topic" exchange type. Queues are assigned a "binding key"
 * when they are bound to an exchange. (The same queue may also be bound more
 * than once to assign multiple binding keys.) When a message is published to
 * the exchange, the exchange routes it to any queue whose binding key matches
 * the message's routing key. Binding keys may have wildcard components to match
 * entire classes of routing keys.
 *
 * SMEDL message routing keys look like this:
 * <channel_name>.<event> (from the environment) or
 * <channel_name>.<monitor>.<event>
 *
 * Only the channel name is significant as far as routing goes.
 *
 * Message content:
 *
 * - The first key in the JSON object is "fmt_version", which must be [2, 0].
 *   The first number is the major version and is incremented any time there is
 *   a backward-incompatible change to the message format. The second number is
 *   the minor version and is incremented any time there is a
 *   backward-compatible update to the message format. Thus, to check for
 *   compatibility, the major version must match, and the minor version must
 *   match or be greater.
 *
 * The other keys:
 *
 * - "name", which is for human reference only but will be
 *   "<monitor>.<event>" for exported events. ("<event>" is recommended for
 *   events from the target system.)
 * - "identities", an array of the monitor identities. For events from the
 *   target system, this should be omitted.
 * - "params", an array of the event parameters.
 * - "aux", which may consist of arbitrary JSON data. If not needed, it should
 *   be set to null.
 *
 * Here is how the various SMEDL types are represented in JSON:
 * - int - Number
 * - char - Number
 * - float - Number
 * - string - String
 * - pointer - String (by converting to uintptr_t and then rendering that in
 *   hexadecimal)
 * - thread - Not supported. Raises UnsupportedFeature.
 *   opaque - String
 */
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>

#include <amqp.h>
#include <amqp_framing.h>
#include <amqp_tcp_socket.h>

#include "cJSON.h"
#include "smedl_types.h"
#include "{{syncset}}_global_wrapper.h"
#include "{{syncset}}_rabbitmq.h"

/* TODO This is how the main program identifies that a SIGTERM has been
 * received. Modify as necessary to work on Windows and write the signal
 * handler. */
static volatile int interrupted = 0;

/* Return nonzero if the program has been asked to terminate (e.g. by SIGTERM
 * on Unix-like systems), zero otherwise. Determines when the main loop should
 * end. */
int is_interrupted() {
    return interrupted;
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
static int check_reply(InitStatus *init_status, RabbitMQState *rmq_state,
        amqp_rpc_reply_t reply, const char *fmt, ...) {
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
                    details->reply_code, details->reply_text.len,
                    details->reply_text.bytes);
            /* Respond */
            amqp_channel_close_ok_t close_ok;
            int status = amqp_send_method(rmq_state->conn, rmq_state->channel,
                    AMQP_CHANNEL_CLOSE_OK_METHOD, &close_ok);
            check_status(status, "Could not send channel_close_ok");
            /* Channel is closed. */
            init_status->channel = 0;

        } else if (reply.reply.id == AMQP_CONNECTION_CLOSE_METHOD) {
            /* Connection error from server */
            amqp_connection_close_t *details =
                (amqp_connection_close_t *) reply.reply.decoded;
            fprintf(stderr, ": Connection error from server: %u %.*s\n"
                    details->reply_code, details->reply_text.len,
                    details->reply_text.bytes);
            /* Respond */
            amqp_connection_close_ok_t close_ok;
            int status = amqp_send_method(rmq_state->conn, 0,
                    AMQP_CONNECTION_CLOSE_OK_METHOD, &close_ok);
            check_status(status, "Could not send connection_close_ok");
            /* Connection is closed */
            init_status->channel = 0;
            init_status->conn = 0;

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

/* Verify that the format version is compatible, i.e. the object is an array of
 * two numbers, where the first (the major version) matches and the second (the
 * minor version) is equal or greater. Return nonzero if so, zero if not. */
static int verify_fmt_version(cJSON *fmt) {
    cJSON *fmt_item;
    if (!cJSON_IsArray(fmt)) {
        err("Bad message ('fmt_version' not present as an array of two "
                "numbers)");
        return 0;
    }

    if (cJSON_ArrayFirst(fmt, fmt_item) && cJSON_IsNumber(fmt_item)) {
        if (fmt_item->valueint != FMT_VERSION_MAJOR) {
            err("Incompatible fmt_version. Expected %d.%d - %d.x",
                    FMT_VERSION_MAJOR, FMT_VERSION_MINOR, FMT_VERSION_MAJOR);
            return 0;
        } else {
            err("Bad message ('fmt_version' not array of two numbers)");
            return 0;
        }
    }

    if (cJSON_ArrayNext(fmt_item) && cJSON_IsNumber(fmt_item)) {
        if (fmt_item->valueint < FMT_VERSION_MINOR) {
            err("Incompatible fmt_version. Expected %d.%d - %d.x",
                    FMT_VERSION_MAJOR, FMT_VERSION_MINOR, FMT_VERSION_MAJOR);
            return 0;
        } else {
            err("Bad message ('fmt_version' not array of two numbers)");
            return 0;
        }
    }

    if (cJSON_ArrayNext(fmt_item)) {
        err("Bad message ('fmt_version' not array of two numbers)");
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
        buf[i] = rk[i] == '\0' ? ' ' : rk[i];
    }
    buf[i] = '\0';
}

/* Handle an incoming message by calling the proper global wrapper import
 * function. Return nonzero on success, zero on failure. */
int handle_message(amqp_envelope_t *envelope) {
    //TODO ACK

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
    routing_key_to_channel(envelope->routing_key, routing_key, {{ch_len}});

    /* Parse JSON */
    //TODO Remove null chars from data?
    cJSON *msg = cJSON_ParseWithLength(envelope->message.body.bytes,
            envelope->message.body.len);
    if (msg == NULL) {
        err("Received message with invalid JSON");
        return 0;
    }

    /* Verify fmt_version */
    cJSON *fmt = cJSON_GetObjectItemCaseSensitive(msg, "fmt_version");
    if (!verify_fmt_version(fmt)) {
        goto fail;
    }

    /* Get event parameters JSON */
    cJSON *params_json = cJSON_GetObjectItemCaseSensitive(msg, "params");
    if (!cJSON_IsArray(params_json)) {
        err("Bad message ('params' not present as an array)");
        goto fail;
    }

    /* Get aux data JSON and convert to SMEDLAux */
    SMEDLAux aux;
    cJSON *aux_json = cJSON_GetObjectItemCaseSensitive(msg, "aux");
    if (aux_json == NULL) {
        err("Bad message ('aux' not present)");
        goto fail;
    }
    /* The returned JSON string is null-terminated, so no need for aux.len */
    aux.data = cJSON_PrintUnformatted(aux_json);
    if (aux.data == NULL) {
        err("Could not serialize aux data");
        goto fail;
    }
    {% for conn in sys.imported_channels(syncset) %}

    {% if conn.source_mon is not none %}
    /* Import {{conn.source_mon.name}}.{{conn.source_event}} */
    {% else %}
    /* Import {{conn.source_event}} (from target system) */
    {% endif %}
    {%+ if not loop.first %}} else {%+ endif -%}
    if (!strcmp(channel, "{{conn.channel}}")) {
        //TODO Need source mon identity types and source event param types
        {% if conn.source_mon is not none %}
        /* Get monitor identities JSON and convert to SMEDLValue array */
        cJSON *id_json;
        cJSON *identities_json = cJSON_GetObjectItemCaseSensitive(msg, "identities");
        if (!cJSON_IsArray(identities_json)) {
            err("Bad message ('identities' not present as an array)");
            goto fail;
        }
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
            char *endptr;
            errno = 0;
            uintptr_t ptr = strtol(id_json->valuestring, &endptr, 16);
            if (errno) {
                err("Could not extract pointer from 'identities': Overflow");
                goto fail;
            } else if (id_json->valuestring[0] == '\0' || *end_ptr != '\0') {
                err("Bad message (Pointer in 'identities' expects "
                        "hexadecimal string)");
                goto fail;
            }
            identities[{{loop.index0}}].v.p = (void *) ptr;
        {% elif param is sameas SmedlType.THREAD %}
        {% unsupported "'thread' type cannot be transported over RabbitMQ" %}
        {% elif param is sameas SmedlType.OPAQUE %}
        if ({{get_next}} && cJSON_IsString(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_OPAQUE;
            identities[{{loop.index0}}].v.o.data = id_json->valuestring;
            identities[{{loop.index0}}].v.o.size = strlen(id_json->valuestring);
        {% endif %}
        } else {
            err("Bad message (Bad 'identities' array)");
            goto fail;
        }
        {% endfor %}
        if (!cJSON_ArrayNext(id_json)) {
            err("Bad message (Too many elements in 'identities' array)");
            goto fail;
        }
        {% else %}
        SMEDLValue *identities = NULL;
        {% endif %}

        /* Convert event parameters to SMEDLValue array */
        //TODO We have a problem. Some events come from the target system. We
        // don't have types for those events.
        SMEDLValue params[{{conn.source_mon.params|length}}];
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
            char *endptr;
            errno = 0;
            uintptr_t ptr = strtol(id_json->valuestring, &endptr, 16);
            if (errno) {
                err("Could not extract pointer from 'identities': Overflow");
                goto fail;
            } else if (id_json->valuestring[0] == '\0' || *end_ptr != '\0') {
                err("Bad message (Pointer in 'identities' expects "
                        "hexadecimal string)");
                goto fail;
            }
            identities[{{loop.index0}}].v.p = (void *) ptr;
        {% elif param is sameas SmedlType.THREAD %}
        {% unsupported "'thread' type cannot be transported over RabbitMQ" %}
        {% elif param is sameas SmedlType.OPAQUE %}
        if ({{get_next}} && cJSON_IsString(id_json)) {
            identities[{{loop.index0}}].t = SMEDL_OPAQUE;
            identities[{{loop.index0}}].v.o.data = id_json->valuestring;
            identities[{{loop.index0}}].v.o.size = strlen(id_json->valuestring);
        {% endif %}
        } else {
            err("Bad message (Bad 'identities' array)");
            goto fail;
        }
        {% endfor %}
        if (!cJSON_ArrayNext(id_json)) {
            err("Bad message (Too many elements in 'identities' array)");
            goto fail;
        }
        //TODO
    }
    {% endfor %}

    /* Cleanup */
    cJSON_Delete(msg);
    return 1;

fail:
    cJSON_Delete(msg);
    return 0;
}

/* While waiting for a regular message, occasionally a non-Basic.Deliver frame
 * will arrive. That frame must be processed before continuing. This function
 * does that. Returns nonzero on success, zero on failure. */
int handle_other_frame(InitStatus *init_status, RabbitMQState *rmq_state) {
    int status;
    amqp_frame_t frame;
    struct timeval timeout = {
        .tv_sec = 0,
        .tv_usec = 0
    };

    /* Read the frame with zero timeout */
    status = amqp_simple_wait_frame_noblock(rmq_state->conn, &frame, &timeout);
    if (status == AMQP_STATUS_TIMEOUT) {
        /* A message should have been ready. Something is wrong. */
        err("Internal error: unable to retrieve frame");
        return 0;
    } else if (!check_status(status, "Could not retrieve frame")) {
        return 0;
    }
#ifdef DEBUG
    if (frame.frame_type == AMQP_FRAME_METHOD) {
        printf("Received unexpected frame: id %u\n", froma.payload.method.id);
    }
#endif //DEBUG

    //TODO If using publisher confirms, those will likely end up here. Either
    // adjust this function or the main loop to handle it.

    return 1;
}

/* Main loop: Start consuming events. Return nonzero on success (when triggered
 * by a signal), zero on failure. */
int consume_events(InitStatus *init_status, RabbitMQState *rmq_state) {
    int status;
    amqp_rpc_reply_t reply;
    amqp_envelope_t envelope;
    /* Note: amqp.h contains a forward declaration for struct timeval */
    struct timeval timeout;
    int error = 0;

    /* Start consuming */
    amqp_basic_consume(rmq_state->conn, rmq_state->channel, rmq_state->queue,
            amqp_empty_bytes, 0, 0, 0, amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state->conn);
    if (!check_reply(init_status, rms_state, reply,
                "Could not start consuming events")) {
        return 0;
    }

    /* MAIN LOOP */
    while (!is_interrupted() && !error) {
        /* Clean up a little */
        amqp_maybe_release_buffers(rmq_state->conn);

        /* Try to consume a message */
        timeval.tv_sec = 5;
        timeval.tv_usec = 0;
        reply = amqp_consume_message(rmq_state->conn, &envelope, &timeout, 0);

        /* Check for timeout, unexpected frame, and errors */
        if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION &&
                reply.library_error == AMQP_STATUS_TIMEOUT) {
            /* Timeout. Nothing to do. */
        } else if (reply.reply_type == AMQP_RESPONSE_LIBRARY_EXCEPTION &&
                reply.library_error == AMQP_STATUS_UNEXPECTED_FRAME) {
            /* Received some frame besides Basic.Deliver. Handle it. */
            if (!handle_other_frame(init_status, rmq_state)) {
                error = 1;
            }
        } else if (check_reply(init_status, rmq_state, reply,
                    "Could not consume message")) {
            /* Message successfully received. Handle it. */
            if (!handle_message(&envelope)) {
                error = 1;
            }
            amqp_destroy_envelope(&envelope);
        } else {
            /* Other error. Exit the loop. */
            error = 1;
        }
    }

    return 1;
}

/* Initialize RabbitMQ. Return nonzero on success, zero on failure. */
int init_rabbitmq(InitStatus *init_status, RabbitMQState *rmq_state,
        RabbitMQConfig *rmq_config) {
    int status;
    amqp_rpc_reply_t reply;
    amqp_socket_t *socket = NULL;
    
    /* Initialize connection */
    rmq_state->conn = amqp_new_connection();
    if (rmq_state->conn == NULL) {
        err("Could not create connection");
        return 0;
    }

    /* Create socket */
    socket = amqp_tcp_socket_new(rmq_state->conn);
    if (socket == NULL) {
        err("Could not create TCP socket");
        return 0;
    }
    init_status->conn_new = 1;

    /* Open socket */
    status = amqp_socket_open(socket, rmq_config->hostname, rmq_config->port);
    if (!check_status(status, "Could not open TCP socket")) {
        return 0;
    }

    /* Login */
    reply = amqp_login(rmq_state->conn, rmq_config->vhost, 0,
            AMQP_DEFAULT_FRAME_SIZE, 0, AMQP_SASL_METHOD_PLAIN,
            rmq_config->username, rmq_config->password);
    if (!check_reply(init_status, rmq_state, reply, "Could not log in")) {
        return 0;
    }
    init_status->conn = 1;

    /* Open channel */
    amqp_channel_open(rmq_state->conn, rmq_state->channel);
    reply = amqp_get_rpc_reply(rmq_state->conn);
    if (!check_reply(init_status, rmq_state, reply, "Could not open channel")) {
        return 0;
    }
    init_status->channel = 1;

    /* Declare the exchange, ensuring it exists */
    amqp_exchange_declare(rmq_state->conn, rmq_state->channel,
            amqp_cstring_bytes(rmq_config->exchange),
            amqp_cstring_bytes("topic"), 0, 0, 1, 0, amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state->conn);
    if (!check_reply(init_status, rmq_state, reply,
                "Could not declare exchange")) {
        return 0;
    }

    /* Create our queue */
    amqp_queue_declare_ok_t *q_ok = amqp_queue_declare(rmq_state->conn,
            rmq_state->channel, amqp_empty_bytes, 0, 0, 1, 1, amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state->conn);
    if (!check_reply(init_status, rmq_state, reply,
                "Could not declare queue")) {
        return 0;
    }
    rmq_state->queue = amqp_bytes_malloc_dup(q_ok->queue);
    if (rmq_state->queue.bytes == NULL) {
        err("Could not store queue name: Out of memory");
        return 0;
    }
    init_status->queue = 1;

    /* Bind our queue to routing keys starting with channel names we import */
    {% for conn in sys.imported_channels(syncset) %}
    amqp_queue_bind(rmq_state->conn, rmq_state->channel, rmq_state->queue,
            amqp_cstring_bytes(exchange),
            amqp_cstring_bytes("{{conn.channel}}.#"), amqp_empty_table);
    reply = amqp_get_rpc_reply(rmq_state->conn);
    if (!check_reply(init_status, rmq_state, reply,
                "Could not bind queue for {{conn.channel}}")) {
        return 0;
    }
    {% endfor %}

    return 1;
}

/* Do all initialization. Return nonzero on success, zero on failure */
int init(InitStatus *init_status, RabbitMQState *rmq_state,
        RabbitMQConfig *rmq_config) {
    /* Init RabbitMQ first */
    if (!init_rabbitmq(init_status, rmq_state, rmq_config)) {
        return 0;
    }

    /* If successful, initialize the synchronous set */
    init_{{syncset}}_syncset();
    init_status->syncset = 1;
    return 1;
}

/* Do RabbitMQ cleanup. Use init_status to determine what needs to be cleaned
 * up. Return nonzero on success, zero on failure. */
int cleanup_rabbitmq(InitStatus *init_status, RabbitMQState *rmq_state) {
    int status, result = 1;
    amqp_rpc_reply_t reply;

    /* Free queue name memory */
    if (init_status->queue) {
        amqp_bytes_free(rmq_state->queue);
    }

    /* Close channel */
    if (init_status->channel) {
        reply = amqp_channel_close(rmq_state->conn, rmq_state->channel,
                AMQP_REPLY_SUCCESS);
        if (!check_reply(init_status, rmq_state, reply,
                    "Could not close channel")) {
            result = 0;
        }
    }

    /* Close the connection */
    if (init_status->conn) {
        reply = amqp_connection_close(rmq_state->conn, AMQP_REPLY_SUCCESS);
        if (!check_reply(init_status, rmq_state, reply,
                    "Could not close connection")) {
            result = 0;
        }
    }

    /* Destroy the connection */
    if (init_status->conn_new) {
        status = amqp_destroy_connection(rmq_state->conn);
        if (!check_status(status, "Could not destroy connection")) {
            result = 0;
        }
    }

    return result;
}

/* Do cleanup. Use init_status to determine what needs to be cleaned up. Return
 * nonzero on success, zero on failure. */
int cleanup(InitStatus *init_status, RabbitMQState *rmq_state) {
    int status = 1;
    if (init_status->syncset) {
        free_{{syncset}}_syncset();
    }

    if (!cleanup_rabbitmq(init_status, rmq_state)) {
        status = 0;
    }

    return status;
}

int main(int argc, char **argv) {
    int status;
    InitStatus init_status = {0};
    RabbitMQState rmq_state = {.channel = 1};
    //TODO Read RabbitMQ config somehow
    RabbitMQConfig rmq_config = {
        .hostname = "localhost",
        .port = 5672,
        .username = "guest",
        .password = "guest",
        .exchange = "smedl.{{sys.name}}",
        .vhost = "/"
    };

    /* Initialize */
    status = init(&init_status, &rmq_state, &rmq_config);

    /* Start consuming events if initialization was successful */
    if (status) {
        status = consume_events(&init_status, &rmq_state);
    }

    if (status) {
        /* Something failed. Clean up. */
        cleanup(&init_status, &rmq_state);
    } else {
        /* Program was terminated. Clean up. */
        status = cleanup(&init_status, &rmq_state, &rmq_config);
    }

    return !status;
}
