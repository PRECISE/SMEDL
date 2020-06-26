#ifndef FILE_H
#define FILE_H

/* Includes jsmn.h with proper #defines */
#include "json.h"

/* Print a message to stderr followed by a newline. Arguments like printf. */
void err(const char *fmt, ...);

/* Status codes for JSONParser */
typedef enum {
    JSONSTATUS_NORMAL,  /* All normal */
    JSONSTATUS_EOF,     /* End of file before another message could be read */
    JSONSTATUS_READERR, /* Read error */
    JSONSTATUS_INVALID, /* Invalid JSON */
    JSONSTATUS_NOMEM    /* Out of memory */
} JSONStatus;

/* Parser state struct. Initialize with init_parser() */
typedef struct JSONParser {
    FILE *f;
    jsmn_parser parser;
    jsmntok_t *tokens;
    size_t tokens_size;
    char *buf;
    size_t buf_size;
    size_t buf_wpos; /* Buffer write position (end of most recent fread) */
    size_t buf_rpos; /* Buffer read position (end of most recent object) */

    /* The following can be queried after init_parser */
    size_t msg_count; /* Number of messages that have been parsed */
    JSONStatus status; /* Will indicate why next_message() returned NULL */
} JSONParser;

/* Struct to store aux data */
typedef struct {
    const char *data;
    size_t len;
} AuxData;

/* Initialize a parser reading from the named file. Returns nonzero if
 * successful, zero on failure. Cleanup with free_parser(). */
int init_parser(JSONParser *parser, const char *fname);

/* Fetch the next message. If successful, returns an array of jsmntok_t
 * containing the parsed message. If there is an error or no more tokens,
 * return NULL. The reason for a NULL return can be determined by checking
 * parser->status.
 *
 * parser - Pointer to the JSONParser to use
 * str - Pointer to string that will be pointed to the JSON text that was
 *   parsed */
jsmntok_t * next_message(JSONParser *parser, char **str);

/* Clean up the provided parser. Returns nonzero if successful, zero on failure.
 */
int free_parser(JSONParser *parser);

/* Print a null-terminated string with characters escaped if JSON requires it */
void print_escaped(const char *str);

/* Print a string of given length with characters escaped if JSON requires it */
void print_escaped_len(const char *str, size_t len);

#endif /* FILE_H */
