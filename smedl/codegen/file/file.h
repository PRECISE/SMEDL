#ifndef {{sys.name}}_FILE_H
#define {{sys.name}}_FILE_H

#include "file.h"

/* Current message format version. Increment the major version whenever making
 * a backward-incompatible change to the message format. Increment the minor
 * version whenever making a backward-compatible update to the message format.
 */
#define FMT_VERSION_MAJOR 2
#define FMT_VERSION_MINOR 0

/* Sample message formats:
 * {
 *     "fmt_version": [2, 0],
 *     "channel": "<channel name>",
 *     "event": "<event>",
 *     "params": [2.5, "some_other_string", 6],
 *     "aux": {
 *         "arbitrary": "json data"
 *      }
 * } 
 *
 * {
 *     "fmt_version": [2, 0],
 *     "channel": "<channel name>",
 *     "event": "<monitor>.<event>",
 *     "identities": [1, "some_string"],
 *     "params": [2.5, "some_other_string", 6],
 *     "aux": {
 *         "arbitrary": "json data"
 *      }
 *  } 
 */

/* System-wide channel enum */
typedef enum {
    {% for channel in sys.imported_connections.keys() %}
    SYSCHANNEL_{{channel}},
    {% endfor %}
    {% for decl in mon_decls %}
    {% for channel in decl.connections.keys() %}
    SYSCHANNEL_{{channel}},
    {% endfor %}
    {% endfor %}
} ChannelID;

/* Queue processing function - Pop events off the queue and send them to the
 * proper synchronous sets (or to be written to the output file) until the
 * queue is empty */
void handle_queue();

/* "Callbacks" (not used as such) for events read from the input file and
 * callbacks for events exported from global wrappers */
{% for channel in sys.imported_connections.keys() %}
void enqueue_{{channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.connections.values() if conn.inter_syncsets is nonempty %}
void enqueue_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

/* Output functions for events that are "sent back to the target system."
 * Return nonzero on success, zero on failure. */
{% for decl in mon_decls %}
{% for conn in decl.connections.values() if none in conn.inter_syncsets %}
int write_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

/* Initialize the global wrappers and register callback functions with them. */
void init_global_wrappers();

/* Receive and process events from the provided JSON parser. Any malformed
 * events are skipped (with a warning printed to stderr). */
void read_events(JSONParser *parser);

/* Verify the fmt_version and retrieve the other necessary components
 * (channel, params, aux). Return nonzero if successful, zero if something is
 * missing or incorrect.
 * Note that aux is not required and will be set to NULL if not given.*/
int get_json_components(const char *str, jsmntok_t *msg,
        jsmntok_t **channel, jsmntok_t **params, jsmntok_t **aux);

#endif /* {{sys.name}}_FILE_H */
