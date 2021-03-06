#ifndef {{syncset}}_MANAGER_H
#define {{syncset}}_MANAGER_H

{% if pure_async %}
#include <signal.h>
{% endif %}
#include "smedl_types.h"

/******************************************************************************
 * External Interface                                                         *
 ******************************************************************************/
{% if not pure_sync %}
{% if pure_async %}

/* Some transports (e.g. ROS) will check for command line arguments from these
 * variables. They are set from main's argc and argv. */
{% else %}
/* Some transports (e.g. ROS) will check for command line arguments from these
 * variables. Sensible defaults are provided, but the target program can
 * override them if desired. */
{% endif %}
extern int smedl_argc;
extern char **smedl_argv;
{% endif %}

/* Initialization interface - Initialize the manager and the attached global
 * wrapper{% if pure_sync %}.{% else %} and network interfaces.{% endif +%}
 *
 * Returns nonzero on success, zero on failure. */
int init_manager(void);

/* Cleanup interface - Tear down and free resources used by the manager and the
 * global wrapper{% if pure_sync %}.{% else %} and network interfaces attached to it.{% endif %} */
void free_manager(void);

{% if pure_async %}
/* Run interface - This is a pure asynchronous manager (no PEDL events are
 * attached synchronously). Run until the program is interrupted with SIGINT
 * or SIGTERM (or smedl_interrupted is set to nonzero, the action taken by
 * the handlers for these signals).
 *
 * Returns nonzero on success and zero on failure. */
{% else %}
{% if not pure_sync %}
/* Run interface - Process all pending events in all attached synchronous sets.
{% else %}
/* Run interface - Process all pending events in all attached synchronous sets
 * and network interfaces.
{% endif %}
 *
 * Returns nonzero on success and zero on failure. */
{% endif %}
int run_manager(void);

{% if not pure_sync %}
/* Manager queueing interfaces - Queue events to be forwarded to monitors or
 * network interfaces.
 *
 * Returns nonzero on success and zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}
int report_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

{% endif %}
/******************************************************************************
 * End of External Interface                                                  *
 ******************************************************************************/
{% if not pure_sync %}
{% if pure_async %}

/* Set to 1 to initiate clean shutdown. */
extern volatile sig_atomic_t smedl_interrupted;
{% if cpp %}

/* Entry point. Allows main() to be in C++ code, but it should do nothing more
 * than call this function and return the result. See:
 * https://isocpp.org/wiki/faq/mixing-c-and-cpp#overview-mixing-langs */
int c_main(int argc, char **argv);
{% endif %}
{% endif %}

/* Queue processing function - Deliver the events in the manager queue to their
 * destinations.
 *
 * Returns nonzero on success and zero on failure. */
int process_queue(void);

/* Manager routing functions - One for each event entering or leaving the
 * synchronous set. Called to route each event from the queue appropriately to
 * the global wrapper or network interfaces.
 *
 * Returns nonzero on success, zero on failure. */
{% for conn in sys.imported_channels(syncset) %}
int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}
{% for conn in sys.exported_channels(syncset).keys() %}
int deliver_{{conn.mon_string}}_{{conn.source_event}}(SMEDLValue *identities, SMEDLValue *params, void *aux);
{% endfor %}

{% endif %}

#endif /* {{syncset}}_MANAGER_H */
