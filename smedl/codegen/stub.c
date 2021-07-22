#include <stdio.h>
#include <string.h>
#include "smedl_types.h"
#include "{{syncset}}_global_wrapper.h"
#include "{{syncset}}_manager.h"
#include "{{syncset}}_stub.h"

/* Functions to handle events returned to the target system */
{% for conn, targets in sys.dest_channels(syncset).items() %}
{% for target in targets if target.target_type == 'export' %}

int perform_{{target.mon_string}}_{{target.event}}(SMEDLValue *ids, SMEDLValue *params, void *aux) {
    printf("{{target.event}}
        {%- for param, dest_type in target.event_params_w_types -%}
        {%- if param.index is none %},NULL
        {%- elif dest_type is sameas SmedlType.INT %},%d
        {%- elif dest_type is sameas SmedlType.FLOAT %},%lf
        {%- elif dest_type is sameas SmedlType.CHAR %},%c
        {%- elif dest_type is sameas SmedlType.STRING %},%s
        {%- elif dest_type is sameas SmedlType.POINTER %},%p
        {%- elif dest_type is sameas SmedlType.OPAQUE %},%*.*s
        {%- endif %}
        {%- endfor %}\n"
        {%- for param, dest_type in target.event_params_w_types %}
        {% if param.index is not none %}
        {% if dest_type is sameas SmedlType.INT %},
        params[{{loop.index0}}].v.i
        {%- elif dest_type is sameas SmedlType.FLOAT %},
        params[{{loop.index0}}].v.d
        {%- elif dest_type is sameas SmedlType.CHAR %},
        params[{{loop.index0}}].v.c
        {%- elif dest_type is sameas SmedlType.STRING %},
        params[{{loop.index0}}].v.s
        {%- elif dest_type is sameas SmedlType.POINTER %},
        params[{{loop.index0}}].v.p
        {%- elif dest_type is sameas SmedlType.OPAQUE %},
        (int) params[{{loop.index0}}].v.o.size,
        (int) params[{{loop.index0}}].v.o.size,
        (char *) params[{{loop.index0}}].v.o.data
        {%- endif %}
        {% endif %}
        {% endfor %});
    return 1;
}
{% endfor %}
{% endfor %}

/* Functions to emit events to SMEDL
 * Params named x* are not used. They can be changed to whatever type is
 * convenient. */
{% for event, conn in sys.ev_imported_connections.items() if conn.syncset.name == syncset %}

int emit_pedl_{{event}}(
{%- for param in conn.source_event_params %}
{% if param is none %}
void *x{{loop.index0}}
{%- elif param is sameas SmedlType.INT %}
int p{{loop.index0}}
{%- elif param is sameas SmedlType.FLOAT %}
double p{{loop.index0}}
{%- elif param is sameas SmedlType.CHAR %}
char p{{loop.index0}}
{%- elif param is sameas SmedlType.STRING %}
char *p{{loop.index0}}
{%- elif param is sameas SmedlType.POINTER %}
void *p{{loop.index0}}
{%- elif param is sameas SmedlType.OPAQUE %}
SMEDLOpaque p{{loop.index0}}
{% endif %}
{% if not loop.last %}, {% endif %}
{%- endfor -%}
) {
    SMEDLValue params[{{conn.source_event_params|length}}];
    {% for param in conn.source_event_params %}
    {% if param is none %}
    params[{{loop.index0}}].t = SMEDL_NULL;
    {% elif param is sameas SmedlType.INT %}
    params[{{loop.index0}}].t = SMEDL_INT;
    params[{{loop.index0}}].v.i = p{{loop.index0}};
    {% elif param is sameas SmedlType.FLOAT %}
    params[{{loop.index0}}].t = SMEDL_FLOAT;
    params[{{loop.index0}}].v.d = p{{loop.index0}};
    {% elif param is sameas SmedlType.CHAR %}
    params[{{loop.index0}}].t = SMEDL_CHAR;
    params[{{loop.index0}}].v.c = p{{loop.index0}};
    {% elif param is sameas SmedlType.STRING %}
    params[{{loop.index0}}].t = SMEDL_STRING;
    params[{{loop.index0}}].v.s = p{{loop.index0}};
    {% elif param is sameas SmedlType.POINTER %}
    params[{{loop.index0}}].t = SMEDL_POINTER;
    params[{{loop.index0}}].v.p = p{{loop.index0}};
    {% elif param is sameas SmedlType.OPAQUE %}
    params[{{loop.index0}}].t = SMEDL_OPAQUE;
    params[{{loop.index0}}].v.o = p{{loop.index0}};
    {% endif %}
    {% endfor %}

    if (!raise_pedl_{{event}}(NULL, params, NULL)) {
#if DEBUG >= 1
        fprintf(stderr, "Could not raise {{event}} event\n");
#endif
        return 0;
    }

    return 1;
}
{% endfor %}

/******************************************************************************
 * Sample code to read from limited CSV is below.
 *
 * Note: Since this is meant as a proof-of-concept, only unquoted strings and
 * opaques are supported, and they may not contain commas. Pointers must be in
 * an implementation-defined format (the format printf() uses for %p).
 ******************************************************************************/

#ifdef _WIN32
#include <windows.h>
#define sleep(x) Sleep((x) * 1000)
#else
#include <unistd.h>
#endif
{% if sys.ev_imported_connections.values()|selectattr('syncset.name', 'equalto', syncset)|list is not nonempty %}
#include <signal.h>

volatile sig_atomic_t interrupted = 0;

/* Signal handler for SIGINT and SIGTERM to shutdown gracefully. Sets the
 * interrupted flag to 1. */
static void set_interrupted(int signum) {
    /* Windows and some other platforms reset the signal handler to the default
     * when a signal is received. Set it back to this function. This creates a
     * race condition on these platforms, but more reliable functions are not
     * cross platform (not that all platforms handle signal() the same way
     * either, or even use SIGINT and SIGTERM at all, but at least they are
     * standard C). Anyway, the worst case scenario is two SIGINT/SIGTERM
     * arrive back to back, the second arrives before the signal handler is
     * set back to this function, and the program is terminated immediately
     * instead of shutting down cleanly. The only thing lost is notifying the
     * server of our exit so it can clean up before it notices we died. */
    signal(signum, set_interrupted);
    interrupted = 1;
}
{% endif %}

int main(int argc, char **argv) {
    if (!init_manager()) {
        fprintf(stderr, "Could not initialize {{syncset}} manager.\n");
        return 1;
    }

    {% if sys.ev_imported_connections.values()|selectattr('syncset.name', 'equalto', syncset)|list is nonempty %}
    {% set ev_len = sys.ev_imported_connections.keys()|map('length')|max + 1 %}
    char event[{{ev_len + 1}}];
    char line[4096];
    int lineno = 1;
    while (fgets(line, sizeof(line), stdin)) {
        /* Read event type */
        if (sscanf(line, "%{{ev_len}}[^,\n]", event) != 1) {
#if DEBUG >= 1
            fprintf(stderr, "Malformed line: %d\n", lineno);
#endif
            lineno++;
            continue;
        }

        /* Call the event's emit function */

        {% for event, conn in sys.ev_imported_connections.items() if conn.syncset.name == syncset %}
        {%+ if not loop.first %}} else {% endif -%}
        if (!strcmp(event, "{{event}}")) {
            {% for param in conn.source_event_params %}
            {% if param is none %}
            {% elif param is sameas SmedlType.INT %}
            int p{{loop.index0}};
            {% elif param is sameas SmedlType.FLOAT %}
            double p{{loop.index0}};
            {% elif param is sameas SmedlType.CHAR %}
            char p{{loop.index0}};
            {% elif param is sameas SmedlType.STRING %}
            char p{{loop.index0}}[4096];
            {% elif param is sameas SmedlType.POINTER %}
            void *p{{loop.index0}};
            {% elif param is sameas SmedlType.OPAQUE %}
            char p{{loop.index0}}buf[4096];
            SMEDLOpaque p{{loop.index0}};
            p{{loop.index0}}.data = p{{loop.index0}}buf;
            {% endif %}
            {% endfor %}
            if (sscanf(line, "%*[^,\n]
                    {%- for param in conn.source_event_params %}
                    {% if param is none -%},%*[^,\n]
                    {%- elif param is sameas SmedlType.INT -%},%d
                    {%- elif param is sameas SmedlType.FLOAT -%},%lf
                    {%- elif param is sameas SmedlType.CHAR -%},%c
                    {%- elif param is sameas SmedlType.STRING -%},%[^,\n]
                    {%- elif param is sameas SmedlType.POINTER -%},%p
                    {%- elif param is sameas SmedlType.OPAQUE -%},%[^,\n]
                    {%- endif %}
                    {% endfor %}"
                    {%- for param in conn.source_event_params %}
                    {% if param is not none %}
                    {% if param is sameas SmedlType.STRING -%}
                    , p{{loop.index0}}
                    {%- elif param is sameas SmedlType.OPAQUE -%}
                    , p{{loop.index0}}buf
                    {%- else -%}
                    , &p{{loop.index0}}
                    {%- endif %}
                    {% endif %}
                    {% endfor -%}
                ) != {{conn.source_event_params|length}}) {
#if DEBUG >= 1
                fprintf(stderr, "Malformed line: %d\n", lineno);
#endif
                lineno++;
                continue;
            }
            {% for param in conn.source_event_params %}
            {% if param is sameas SmedlType.OPAQUE %}
            p{{loop.index0}}.size = strlen(p{{loop.index0}}.data);
            {% endif %}
            {% endfor %}
            if (!emit_pedl_{{event}}({% for param in conn.source_event_params %}
                {% if param is none %}NULL
                {%- else %}p{{loop.index0}}
                {%- endif %}
                {% if not loop.last %}, {% endif %}
                {% endfor %})) {
                return 3;
            }

        {% endfor %}
        } else {
#if DEBUG >= 2
            fprintf(stderr, "Unknown event %s (line: %d)\n", event, lineno);
#endif
            lineno++;
            continue;
        }

        if (!run_manager()) {
#if DEBUG >= 1
            fprintf(stderr, "Could not run manager (line: %d)\n", lineno);
#endif
            return 4;
        }

        lineno++;
    }

    /* Wait a moment for any remaining events */
    sleep(5);
    if (!run_manager()) {
#if DEBUG >= 1
        fprintf(stderr, "Could not run manager\n");
#endif
        return 4;
    }
    {% else %}
    /* Syncset has no exported events. Run and wait for Ctrl-C. */
    if (signal(SIGINT, set_interrupted) == SIG_ERR) {
        fprintf(stderr, "Could not set SIGINT handler\n");
        return 2;
    }
    if (signal(SIGTERM, set_interrupted) == SIG_ERR) {
        fprintf(stderr, "Could not set SIGTERM handler\n");
        return 2;
    }

    while (!interrupted) {
        if (!run_manager()) {
#if DEBUG >= 1
            fprintf(stderr, "Could not run manager\n");
#endif
            return 4;
        }
        sleep(1);
    }
    {% endif %}

#if DEBUG >= 3
    fprintf(stderr, "Done.\n");
#endif
    free_manager();
    return 0;
}
