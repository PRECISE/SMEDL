#ifndef {{syncset}}_RABBITMQ_H
#define {{syncset}}_RABBITMQ_H

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
 * Only the channel name is significant as far as SMEDL's routing goes (between
 * synchronous sets).
 *
 * Message properties:
 *
 * RabbitMQ messages can have certain properties attached. See:
 * https://www.rabbitmq.com/publishers.html#message-properties
 * These are the properties useful for SMEDL messages:
 *
 * - content-type: Optional, but recommended. Set to "application/json" since
 *   SMEDL messages are JSON-formatted.
 * - correlation-id: Optional. If set on an imported event, it will be
 *   copied to any exported events that result. Can be used by the target
 *   system to link exported events to their cause.
 * - type: Optional, but HIGHLY RECOMMENDED. If used, must be set to
 *   "smedl-fmt<major>.<minor>", where <major> and <minor> are the SMEDL
 *   message format version. E.g. "smedl-fmt2.0". See the FMT_VERSION_* macros
 *   below for the version expected. The major version must equal
 *   FMT_VERSION_MAJOR and the minor version must be >= FMT_VERSION_MINOR.
 *   (The major version is incremented for backward-incompatible changes, the
 *   minor version is incremented for backward-compatible changes.)
 *
 * Message body:
 *
 * The body is a JSON-formatted object. Here are the key-value pairs that
 * should be present:
 *
 * - "event", which is optional and for human reference only but will be
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
 * - opaque - String
 */

#include <amqp.h>

/* Current message format version. Increment the major version whenever making
 * a backward-incompatible change to the message format. Increment the minor
 * version whenever making a backward-compatible update to the message format.
 */
#define FMT_VERSION_MAJOR 2
#define FMT_VERSION_MINOR 0
#define FMT_VERSION_STRING "smedl-fmt2.0"

/* A struct to keep track of what has been initialized and what has not, so
 * cleanup can happen properly */
typedef struct {
    char conn_new;
    char conn;
    char channel;
    char queue;
    char syncset;
} InitStatus;

/* A struct to hold RabbitMQ data such as the connection, channel ID, queue
 * name, etc. */
typedef struct {
    amqp_connection_state_t conn;
    amqp_channel_t channel;
    amqp_bytes_t exchange;
    amqp_bytes_t queue;
} RabbitMQState;

/* A struct to hold all the config data necessary for RabbitMQ */
typedef struct {
    char *hostname;
    unsigned int port;
    char *username;
    char *password;
    char *exchange;
    char *vhost;
} RabbitMQConfig;

/* A struct to hold stored aux data from an incoming message and
 * RabbitMQState, needed when later sending a message out. Used as the aux
 * parameter for SMEDL API calls. */
typedef struct {
    RabbitMQState *state;
    char correlation_id[257];
    void *aux;
} RabbitMQAux;

/* Signal handler for SIGINT and SIGTERM. Set the interrupted flag to nonzero
 * (1 normally, 2 if there was also an error reinstating the signal handler.) */
void set_interrupted(int signum);

/* Handle an incoming message by calling the proper global wrapper import
 * function. Return nonzero on success, zero on failure. */
int handle_message(RabbitMQState *rmq_state, amqp_envelope_t *envelope);

/* Main loop: Start consuming events. Return nonzero on success (when triggered
 * by a signal), zero on failure. */
int consume_events(InitStatus *init_status, RabbitMQState *rmq_state);

/* While waiting for a regular message, occasionally a non-Basic.Deliver frame
 * will arrive. That frame must be processed before continuing. This function
 * does that. Returns nonzero on success, zero on failure. */
int handle_other_frame(InitStatus *init_status, RabbitMQState *rmq_state);

/* Send a message over RabbitMQ. Return nonzero on success, zero on failure. */
int send_message(RabbitMQState *rmq_state, const char *routing_key,
        const char *correlation_id, const char *msg, size_t len);

/* Message send functions - Send an exported message. To be used as the
 * callbacks in the global wrapper. */
{% for decl in mon_decls %}
{% for conn in decl.inter_connections %}
int send_{{syncset}}_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

/* Open the file named "fname" in the current directory, if it exists. Strip
 * out any C++-style comments that are the first non-whitespace on their line.
 * Parse the result as JSON and update the config with any values that were
 * read.
 *
 * If successful, the caller must free the pointer returned through out_buf
 * when the configuration is no longer needed (unless it is NULL).
 *
 * Return nonzero on success or if the file cannot be read, return zero
 * on failure. */
int read_config(const char *fname, RabbitMQConfig *rmq_config, char **out_buf);

/* Do all initialization. Return nonzero on success, zero on failure */
int init(InitStatus *init_status, RabbitMQState *rmq_state,
        RabbitMQConfig *rmq_config);

/* Do cleanup. Use init_status to determine what needs to be cleaned up. Return
 * nonzero on success, zero on failure. */
int cleanup(InitStatus *init_status, RabbitMQState *rmq_state);

/* Initialize RabbitMQ. Return nonzero on success, zero on failure. */
int init_rabbitmq(InitStatus *init_status, RabbitMQState *rmq_state,
        RabbitMQConfig *rmq_config);

/* Do RabbitMQ cleanup. Use init_status to determine what needs to be cleaned
 * up. Return nonzero on success, zero on failure. */
int cleanup_rabbitmq(InitStatus *init_status, RabbitMQState *rmq_state);

#endif /* {{syncset}}_RABBITMQ_H */
