#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <errno.h>
#include "global_event_queue.h"
#include "file.h"
#include "json.h"
{% for syncset in sys.syncsets.values() %}
#include "{{syncset.name}}_global_wrapper.h"
{% endfor %}
#include "{{sys.name}}_file.h"

static GlobalEventQueue queue = {0};

/* Queue processing function - Pop events off the queue and send them to the
 * proper synchronous sets (or to be written to the output file) until the
 * queue is empty */
{# ************************************************************************** #}
{% macro handle(conn) -%}
{% for syncset in conn.inter_syncsets %}
{% if syncset is none %}

success = success && write_{{conn.channel}}(identities, params, aux);
{%- else %}

success = success && import_{{syncset.name}}_{{conn.channel}}(identities, params, aux);
{%- endif %}
{% endfor %}
{% for param in conn.source_event_params %}
{% if param is sameas SmedlType.STRING %}

free(params[{{loop.index0}}].v.s);
{%- elif param is sameas SmedlType.OPAQUE %}

free(params[{{loop.index0}}].v.o.data);
{%- endif %}
{% endfor %}
{% endmacro %}
{# ************************************************************************** #}
int handle_queue() {
    int success = 1;
    int channel;
    SMEDLValue *identities, *params;
    void *aux;

    while (pop_global_event(&queue, &channel, &identities, &params, &aux)) {
        switch (channel) {
            {% for conn in sys.imported_connections.values() %}
            case SYSCHANNEL_{{conn.channel}}:{# Jinja whitespace control -#}
                {{handle(conn)|indent(16)}}
                break;
            {% endfor %}
            {% for decl in mon_decls %}
            {% for conn in decl.connections.values() if conn.inter_syncsets is nonempty %}
            case SYSCHANNEL_{{conn.channel}}:{# Jinja whitespace control -#}
                {{handle(conn)|indent(16)}}
                break;
            {% endfor %}
            {% endfor %}
        }
    }

    /* Event params were malloc'd in the enqueue_*() functions. They are no
     * longer needed. (String and opaque data were already free'd in the
     * switch.) */
    free(params);
    return success;
}

/* "Callbacks" (not used as such) for events read from the input file and
 * callbacks for events exported from global wrappers.
 * Return nonzero on success, zero on failure. */
{% for conn in sys.imported_connections.values() %}

int enqueue_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params,
        void *aux) {
    SMEDLValue *params_copy = smedl_copy_array(params, {{conn.source_event_params|length}});
    if (!push_global_event(&queue, SYSCHANNEL_{{conn.channel}}, identities, params_copy, aux)) {
        /* malloc fail */
        smedl_free_array(params_copy, {{conn.source_event_params|length}});
        return 0;
    }
    return 1;
}
{% endfor %}
{% for decl in mon_decls %}
{% for conn in decl.connections.values() if conn.inter_syncsets is nonempty %}

int enqueue_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params,
        void *aux) {
    SMEDLValue *params_copy = smedl_copy_array(params, {{conn.source_event_params|length}});
    if (!push_global_event(&queue, SYSCHANNEL_{{conn.channel}}, identities, params_copy, aux)) {
        /* malloc fail */
        smedl_free_array(params_copy, {{conn.source_event_params|length}});
        return 0;
    }
    return 1;
}
{% endfor %}
{% endfor %}

/* Output functions for events that are "sent back to the target system."
 * Return nonzero on success, zero on failure. */
{% for decl in mon_decls %}
{% for conn in decl.connections.values() if none in conn.inter_syncsets %}

int write_{{conn.channel}}(SMEDLValue *identities, SMEDLValue *params, void *aux) {
    printf("{\n"
        "\t\"fmt_version\": [%d, %d],\n"
        "\t\"channel\": \"{{conn.channel}}\",\n"
        "\t\"event\": \"{{conn.source_mon.name}}.{{conn.source_event}}\",\n"
        "\t\"identities\": [",
        FMT_VERSION_MAJOR, FMT_VERSION_MINOR);
    {% for param in conn.source_mon.params %}
    {% if param is sameas SmedlType.INT %}
    printf("%d", identities[{{loop.index0}}].v.i);
    {% elif param is sameas SmedlType.FLOAT %}
    printf("%f", identities[{{loop.index0}}].v.d);
    {% elif param is sameas SmedlType.CHAR %}
    printf("%d", identities[{{loop.index0}}].v.c);
    {% elif param is sameas SmedlType.STRING %}
    print_escaped(identities[{{loop.index0}}].v.s);
    {% elif param is sameas SmedlType.POINTER %}
    printf("\"%" PRIxPTR "\"", (uintptr_t) identities[{{loop.index0}}].v.p);
    {% elif param is sameas SmedlType.OPAQUE %}
    print_escaped_len(identities[{{loop.index0}}].v.o.data,
            identities[{{loop.index0}}].v.o.size);
    {% endif %}
    {% if not loop.last %}
    printf(", ");
    {% endif %}
    {% endfor %}
    printf("],\n"
        "\t\"params\": [");
    {% for param in conn.source_event_params %}
    {% if param is sameas SmedlType.INT %}
    printf("%d", params[{{loop.index0}}].v.i);
    {% elif param is sameas SmedlType.FLOAT %}
    printf("%f", params[{{loop.index0}}].v.d);
    {% elif param is sameas SmedlType.CHAR %}
    printf("%d", params[{{loop.index0}}].v.c);
    {% elif param is sameas SmedlType.STRING %}
    print_escaped(params[{{loop.index0}}].v.s);
    {% elif param is sameas SmedlType.POINTER %}
    printf("\"%" PRIxPTR "\"", (uintptr_t) params[{{loop.index0}}].v.p);
    {% elif param is sameas SmedlType.OPAQUE %}
    print_escaped_len(params[{{loop.index0}}].v.o.data,
            params[{{loop.index0}}].v.o.size);
    {% endif %}
    {% if not loop.last %}
    printf(", ");
    {% endif %}
    {% endfor %}
    AuxData *aux_data = aux;
    printf("],\n"
        "\t\"aux\": %.*s\n", (int) aux_data->len, aux_data->data);
    printf("}\n");
    return 0;
}
{% endfor %}
{% endfor %}

/* Verify the fmt_version and retrieve the other necessary components
 * (channel, params, aux). Return nonzero if successful, zero if something is
 * missing or incorrect.
 * Note that aux is not required and will be set to NULL if not given. */
int get_json_components(const char *str, jsmntok_t *msg,
        jsmntok_t **channel, jsmntok_t **params, jsmntok_t **aux) {
    /* Verify fmt_version */
    int version;
    jsmntok_t *fmt_version = json_lookup(str, msg, "fmt_version");
    if (fmt_version == NULL ||
            fmt_version->type != JSMN_ARRAY ||
            fmt_version->size != 2) {
#if DEBUG >= 2
        err("fmt_version not present, not array, or not size 2");
#endif
        return 0;
    }
    if (!json_to_int(str, fmt_version + 1, &version) ||
            version != FMT_VERSION_MAJOR) {
#if DEBUG >= 2
        err("Major fmt_version does not match");
#endif
        return 0;
    }
    if (!json_to_int(str, fmt_version + 2, &version) ||
            version < FMT_VERSION_MINOR) {
#if DEBUG >= 2
        err("Minor fmt_version too low");
#endif
        return 0;
    }

    /* Extract other components */
    *channel = json_lookup(NULL, NULL, "channel");
    if (*channel == NULL || (*channel)->type != JSMN_STRING) {
#if DEBUG >= 2
        err("channel not present or not a string");
#endif
        return 0;
    }
    *params = json_lookup(NULL, NULL, "params");
    if (*params == NULL || (*params)->type != JSMN_ARRAY) {
#if DEBUG >= 2
        err("params not present or not an array");
#endif
        return 0;
    }
    *aux = json_lookup(NULL, NULL, "aux");

    return 1;
}

/* Receive and process events from the provided JSON parser. Any malformed
 * events are skipped (with a warning printed to stderr). */
void read_events(JSONParser *parser) {
    jsmntok_t *msg;
    char *str;

    for (msg = next_message(parser, &str);
            msg != NULL;
            msg = next_message(parser, &str)) {
        /* Get components from JSON */
        jsmntok_t *chan_tok, *params_tok, *aux_tok;
        if (!get_json_components(str, msg, &chan_tok, &params_tok, &aux_tok)) {
            err("\nWarning: Message %d has incorrect format or incompatible "
                    "fmt_version\n",
                    parser->msg_count);
            continue;
        }

        /* Create aux struct */
        AuxData aux;
        aux.data = str + aux_tok->start;
        aux.len = aux_tok->end - aux_tok->start;
        if (aux_tok->type == JSMN_STRING) {
            aux.data--;
            aux.len += 2;
        }

        /* Import the event */
        char *chan;
        size_t chan_len;
        int ch_result = json_to_string_len(str, chan_tok, &chan, &chan_len);
        if (!ch_result) {
            err("\nStopping: Out of memory.");
            break;
        }
        {% for conn in sys.imported_connections.values() %}
        {%+ if not loop.first %}} else {% endif %}if (chan_len == strlen("{{conn.channel}}") &&
                !strncmp(chan, "{{conn.channel}}", chan_len)) {
            /* Check param array length */
            if (params_tok->size < {{conn.source_event_params|length}}) {
            }
            /* Convert params to SMEDLValue array */
            int tmp_i;
            char *tmp_s;
            SMEDLValue params[{{conn.source_event_params|length}}];
            {% for param in conn.source_event_params %}
            params_tok++;
            {% if param is sameas SmedlType.INT %}
            if (json_to_int(str, params_tok, &params[{{loop.index0}}].v.i)) {
                params[{{loop.index0}}].t = SMEDL_INT;
            {% elif param is sameas SmedlType.FLOAT %}
            if (json_to_double(str, params_tok, &params[{{loop.index0}}].v.d)) {
                params[{{loop.index0}}].t = SMEDL_FLOAT;
            {% elif param is sameas SmedlType.CHAR %}
            if (json_to_int(str, params_tok, &tmp_i)) {
                params[{{loop.index0}}].t = SMEDL_CHAR;
                params[{{loop.index0}}].v.c = tmp_i;
            {% elif param is sameas SmedlType.STRING %}
            if (json_to_string(str, params_tok, &params[{{loop.index0}}].v.s)) {
                params[{{loop.index0}}].t = SMEDL_STRING;
            {% elif param is sameas SmedlType.POINTER %}
            if (json_to_string(str, params_tok, &tmp_s)) {
                params[{{loop.index0}}].t = SMEDL_POINTER;
                if (!smedl_string_to_pointer(tmp_s, &params[{{loop.index0}}].v.p)) {
                    err("\nWarning: Skipping message %d: Overflow or bad "
                            "format extracting pointer from params\n",
                            parser->msg_count);
                    free(tmp_s);
                    smedl_free_array_contents(params, {{loop.index0}});
                    continue;
                }
            {% elif param is sameas SmedlType.OPAQUE %}
            if (json_to_opaque(str, params_tok,
                        &params[{{loop.index0}}].v.o.data,
                        &params[{{loop.index0}}].v.o.size)) {
                params[{{loop.index0}}].t = SMEDL_OPAQUE;
            {% elif param is none %}
            params[{{loop.index0}}].t = SMEDL_NULL;
            {% endif %}
            {% if param is not none %}
            } else {
                err("\nWarning: Skipping message %d: Bad format, overflow, or "
                        "out-of-memory\n", parser->msg_count);
                smedl_free_array_contents(params, {{loop.index0}});
                continue;
            }
            {% endif %}
            {% endfor %}

            /* Process the event */
            int result = enqueue_{{conn.channel}}(NULL, params, &aux);
            smedl_free_array_contents(params, {{conn.source_event_params|length}});
            if (result) {
                if (!handle_queue()) {
                    err("\nWarning: Problem processing queue after message %d",
                            parser->msg_count);
                }
            } else {
                err("\nWarning: Skipping message %d: "
                        "enqueue_{{conn.channel}}() failed\n",
                        parser->msg_count);
            }
        {% endfor %}
        }
        if (ch_result < 0) {
            free(chan);
        }
    }

    if (parser->status == JSONSTATUS_READERR) {
        err("\nStopping: Read error.");
    } else if (parser->status == JSONSTATUS_INVALID) {
        err("\nStopping: Encountered malformed message.");
    } else if (parser->status == JSONSTATUS_NOMEM) {
        err("\nStopping: Out of memory.");
    } else if (parser->status == JSONSTATUS_EOF) {
        err("\nFinished.");
    }
    err("Processed %d messages.", parser->msg_count);
}

/* Initialize the global wrappers and register callback functions with them.
 * Return nonzero on success, zero on failure. */
int init_global_wrappers() {
    {% for syncset in sys.syncsets.values() %}
    /* {{syncset.name}} syncset */
    if (!init_{{syncset.name}}_syncset()) {
        goto fail_init_{{syncset.name}};
    }
    {% for decl in syncset %}
    {% for conn in decl.inter_connections %}
    callback_{{syncset.name}}_{{conn.channel}}(enqueue_{{conn.channel}});
    {% endfor %}
    {% endfor %}

    {% endfor %}
    return 1;

    {% for syncset in sys.syncsets.values()|reverse %}
    {% if not loop.first %}
    free_{{syncset.name}}_syncset();
    {% endif %}
fail_init_{{syncset.name}}:
    {% endfor %}
    return 0;
}

/* Print a help message to stderr */
static void usage(const char *name) {
    err("Usage: %s [--] [input.json]", name);
    err("Read messages from the provided input file (or stdin if not provided) "
            "and print\nthe messages emitted back to the environment");
}

int main(int argc, char **argv) {
    /* Check for a file name argument */
    const char *fname = NULL;
    if (argc >= 2) {
        if (!strcmp(argv[1], "--help")) {
            usage(argv[0]);
            return 0;
        } else if (!strcmp(argv[1], "--")) {
            if (argc == 3) {
                fname = argv[2];
            } else {
                usage(argv[0]);
                return 1;
            }
        }
    }


    /* Initialize global wrappers */
    int result = init_global_wrappers();
    if (!result) {
        err("Could not initialize global wrappers");
        return 1;
    }

    /* Initialize the parser */
    JSONParser parser;
    result = init_parser(&parser, fname);
    if (!result) {
        err("Could not initialize JSON parser");
        return 1;
    }

    /* Start handling events */
    read_events(&parser);

    /* Cleanup the parser */
    result = free_parser(&parser);
    if (!result) {
        err("Could not clean up JSON parser");
        return 1;
    }
    return 0;
}
