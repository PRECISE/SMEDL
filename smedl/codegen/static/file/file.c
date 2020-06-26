#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
/* Includes jsmn.h with proper #defines */
#include "json.h"
#include "file.h"

/* Print a message to stderr followed by a newline. Arguments like printf. */
void err(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vfprintf(stderr, fmt, args);
    va_end(args);
    fprintf(stderr, "\n");
}

/* Initialize a parser reading from the named file. Returns nonzero if
 * successful, zero on failure. Cleanup with free_parser(). */
int init_parser(JSONParser *parser, const char *fname) {
    /* Open the file or use stdin */
    if (fname != NULL) {
        parser->f = fopen(fname, "r");
        if (parser->f == NULL) {
            err("Could not open %s for reading", fname);
            return 0;
        }
    } else {
        parser->f = stdin;
    }

    /* Initial token allocation */
    parser->tokens_size = 24;
    parser->tokens = malloc(sizeof(jsmntok_t) * parser->tokens_size);
    if (parser->tokens == NULL) {
        err("Out of memory");
        fclose(parser->f);
        return 0;
    }

    /* Initial buffer allocation */
    parser->buf_size = 128;
    parser->buf_wpos = 0;
    parser->buf_rpos = 0;
    parser->buf = malloc(parser->buf_size);
    if (parser->buf == NULL) {
        err("Out of memory");
        free(parser->tokens);
        fclose(parser->f);
        return 0;
    }

    /* Initialize the jsmn parser */
    jsmn_init(&parser->parser);
    parser->msg_count = 0;
    parser->status = JSONSTATUS_NORMAL;

    return 1;
}

/* Fetch the next message. If successful, returns an array of jsmntok_t
 * containing the parsed message. If there is an error or no more tokens,
 * return NULL. The reason for a NULL return can be determined by checking
 * parser->status.
 *
 * parser - Pointer to the JSONParser to use
 * str - Pointer to string that will be pointed to the JSON text that was
 *   parsed */
jsmntok_t * next_message(JSONParser *parser, char **str) {
    int result;
    parser->msg_count++;

    /* Is there any more data? */
    if (feof(parser->f)) {
        parser->status = JSONSTATUS_EOF;
        return NULL;
    }

    /* Shift the previous message out of the buffer */
    memmove(parser->buf, parser->buf + parser->buf_rpos);
    parser->buf_wpos -= parser->buf_rpos;
    parser->buf_rpos = 0;

    do {
        /* Try to fill the buffer */
        parser->buf_wpos += fread(parser->buf + parser->buf_wpos, 1,
                parser->buf_size - parser->buf_wpos; parser->f);
        if (ferror(parser->f)) {
            err("Read error on input file");
            parser->status = JSONSTATUS_READERR;
            return NULL;
        }
        
        /* Attempt to parse */
        do {
            result = jsmn_parse(&parser->parser, parser->buf, parser->buf_wpos,
                    parser->tokens, parser->tokens_size);
            if (result == JSMN_ERROR_NOMEM) {
                /* Need more tokens */
                parser->tokens_size *= 2;
                jsmntok_t *tmp = realloc(parser->tokens, sizeof(jsmntok_t) *
                        parser->tokens_size);
                if (tmp == NULL) {
                    err("Out of memory");
                    parser->status = JSONSTATUS_NOMEM;
                    return NULL;
                }
                parser->tokens = tmp;
            }
        } while (result == JSMN_ERROR_NOMEM);

        if (result == JSMN_ERROR_PART) {
            /* Need more buffer */
            parser->buf_size *= 2;
            char *tmp = realloc(parser->buf, parser->buf_size);
            if (tmp == NULL) {
                err("Out of memory");
                parser->status = JSONSTATUS_NOMEM;
                return NULL;
            }
            parser->buf = tmp;
        }
    /* Continue until either 1) we have enough tokens and buffer or 2) EOF */
    } while (result == JSMN_ERROR_PART && !feof(parser->f));

    if (result == JSMN_ERROR_PART) {
        /* Reached end of file. Return. */
        parser->status = JSONSTATUS_EOF;
        return NULL;
    } else if (result == JSMN_ERROR_INVAL) {
        /* Invalid JSON. Give up. */
        err("JSON message #%d is invalid", parser->msg_count);
        parser->status = JSONSTATUS_INVALID;
        return NULL;
    }

    /* Success */
    msg_count++;
    parser->buf_rpos += parser->tokens[0].end;
    *str = parser->buf;
    return parser->tokens;
}

/* Clean up the provided parser. Returns nonzero if successful, zero on failure.
 */
int free_parser(JSONParser *parser) {
    free(parser->buf);
    free(parser->tokens);
    if (fclose(parser->f) == EOF) {
        err("Could not close input file");
        return 0;
    }
    return 1;
}

/* Print a null-terminated string with characters escaped if JSON requires it */
void print_escaped(const char *str) {
    fputc('\"', stdout);
    while (*str != '\0') {
        if (*str < 0x32) {
            printf("\\u%.4x", (unsigned) *str);
        } else if (*str == '\\' || *str == '\"') {
            fputc('\\', stdout);
            fputc(*str, stdout);
        } else {
            fputc(*str, stdout);
        }
        str++;
    }
    fputc('\"', stdout);
}

/* Print a string of given length with characters escaped if JSON requires it */
void print_escaped_len(const char *str, size_t len) {
    fputc('\"', stdout);
    for (size_t i = 0; i < len; i++) {
        if (str[i] < 0x32) {
            printf("\\u%.4x", (unsigned) str[i]);
        } else if (str[i] == '\\' || str[i] == '\"') {
            fputc('\\', stdout);
            fputc(str[i], stdout);
        } else {
            fputc(str[i], stdout);
        }
    }
    fputc('\"', stdout);
}
