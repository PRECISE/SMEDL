#ifndef {{sys.name}}_FILE_H
#define {{sys.name}}_FILE_H

#include "system.h"
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

/* Queue processing function - Pop events off the queue and send them to the
 * proper synchronous sets (or to be written to the output file) until the
 * queue is empty */
void handle_queue(SystemEventQueue *q);

/* "Callbacks" (not used as such) for events read from the input file and
 * callbacks for events exported from global wrappers */
{% for channel in sys.imported_connections.keys() %}
enqueue_{{channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for decl in mon_decls %}
{% for channel in decl.connections.keys() %}
enqueue_{{channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% endfor %}

/* Output functions for events that are "sent back to the target system."
 * Return nonzero on success, zero on failure. */
int write_{{channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux);

#endif /* {{sys.name}}_FILE_H */
