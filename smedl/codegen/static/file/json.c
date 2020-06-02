#ifdef DEBUG
#include <stdio.h>
#endif /* DEBUG */

#ifndef JSMN_STRICT
#define JSMN_STRICT
#endif /* JSMN_STRICT */
#ifndef JSMN_PARENT_LINKS
#define JSMN_PARENT_LINKS
#endif /* JSMN_PARENT_LINKS */
#include "jsmn.h"

/* Must come after the jsmn #include and #defines above */
#include "json.h"

/* Lookup a key and return a pointer to the value token. This is most efficient
 * when looking up keys from the same object and in the order in which they
 * appear in the object. Return NULL if the provided token is not an object or
 * the key is not found.
 *
 * Parameters:
 * object - A pointer to the object token. For efficient lookups, use NULL to
 *   look up from the same object in subsequent calls.
 * key - The key to look up, as an escaped string
 */
jsmntok_t * json_lookup(const char *str, jsmntok_t *object, const char *key) {
    static jsmntok_t *start;
    static jsmntok_t *curr;
    static int index, size;

    /* If object was provided, reset everything */
    if (object != NULL) {
        if (object->type != JSMN_OBJECT) {
#ifdef DEBUG
            fprintf(stderr, "Called json_lookup on a non-object token\n");
#endif /* DEBUG */
            return NULL;
        }
        start = object;
        curr = object;
        index = 0;
        /* Size is number of key/value pairs */
        size = object->size;
    }

    /* Search for the key */
    int i = index;
    do {
        if (strncmp(key, str + curr->start, curr->end - curr->start)) {
            /* Found it */
            index = i + 1;
            jsmntok_t *val = curr + 1;
            json_next_key(&val);
            if (index == size) {
                index = 0;
                curr = start;
            }
            return val;
        }
        
        /* Move to the next key */
        json_next_key(&curr);
        i++;
        if (i == size) {
            i = 0;
            curr = start;
        }
    } while (i != index);

    /* Didn't find it */
    return NULL;
}

/* Move token to point at the next sibling. Does not check to see if there
 * actually is a next sibling to point to. */
void json_next(jsmntok_t **token) {
    for (int remaining = 1; remaining > 0; remaining--) {
        /* size is number of key-value pairs for objects, number of elements
         * for arrays, 1 for the key in a key-value pair, 0 otherwise */
        //TODO
    }
    jsmntype_t type = (*token)->type;

    /* Advance past this token */
    (*token)++;

    /* If array or object, advance past children */
    if (type == 
    //TODO
}

/* Move a token pointing to an object key to the next key in the object.
 * Does not check to see if there actually is a next key to point to. */
void json_next_key(jsmntok_t **token) {
    /* Advance past key */
    (*token)++;
    /* Advance past value */
    json_next(token);
}

/* Convert a regular string to an escaped string (or return NULL on failure) */
char * json_escape(const char * str) {
    //TODO
}
