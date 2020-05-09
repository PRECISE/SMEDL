#ifndef {{syncset}}_RABBITMQ_H
#define {{syncset}}_RABBITMQ_H

/* Current message format version. Increment the major version whenever making
 * a backward-incompatible change to the message format. Increment the minor
 * version whenever making a backward-compatible update to the message format.
 */
#define FMT_VERSION_MAJOR 2
#define FMT_VERSION_MINOR 0

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
    amqp_bytes_t queue;
} RabbitMQState;

/* A struct to hold all the config data necessary for RabbitMQ */
typedef struct {
    const char *hostname;
    unsigned int port;
    const char *username;
    const char *password;
    const char *exchange;
    const char *vhost;
} RabbitMQConfig;

/* Return nonzero if the program has been asked to terminate (e.g. by SIGTERM
 * on Unix-like systems), zero otherwise. Determines when the main loop should
 * end. */
int is_interrupted();

/* Handle an incoming message by calling the proper global wrapper import
 * function. Return nonzero on success, zero on failure. */
int handle_message(amqp_envelope_t *envelope);

/* Main loop: Start consuming events. Return nonzero on success (when triggered
 * by a signal), zero on failure. */
int consume_events(InitStatus *init_status, RabbitMQState *rmq_state);

/* While waiting for a regular message, occasionally a non-Basic.Deliver frame
 * will arrive. That frame must be processed before continuing. This function
 * does that. Returns nonzero on success, zero on failure. */
int handle_other_frame(InitStatus *init_status, RabbitMQState *rmq_state);

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
