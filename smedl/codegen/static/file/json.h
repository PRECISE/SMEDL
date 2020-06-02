#ifndef JSON_H
#define JSON_H

/* Except in json.c, jsmn.h should only be included through this file to
 * ensure the #defines are all correct */

#define JSMN_HEADER
#ifndef JSMN_STRICT
#define JSMN_STRICT
#endif /* JSMN_STRICT */
#ifndef JSMN_PARENT_LINKS
#define JSMN_PARENT_LINKS
#endif /* JSMN_PARENT_LINKS */
#include "jsmn.h"

/* Lookup a key and return a pointer to the value token. This is most efficient
 * when looking up keys from the same object and in the order in which they
 * appear in the object. Return NULL if the provided token is not an object or
 * the key is not found.
 *
 * Parameters:
 * str - The string containing JSON data
 * object - A pointer to the object token. For efficient lookups, use NULL to
 *   look up from the same object in subsequent calls.
 * key - The key to look up, as an escaped string
 */
jsmntok_t * json_lookup(jsmntok_t *object, const char *key);

/* Move token to point at the next sibling. Does not check to see if there
 * actually is a next sibling to point to. */
void json_next(jsmntok_t **token);

/* Move a token pointing to an object key to the next key in the object.
 * Does not check to see if there actually is a next key to point to. */
void json_next_key(jsmntok_t **token);

/* Convert a regular string to an escaped string (or return NULL on failure) */
char * json_escape(const char * str);

/* Functions to convert tokens to int, double, string */

#end /* JSON_H */
