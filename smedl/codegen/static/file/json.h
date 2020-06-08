#ifndef JSON_H
#define JSON_H

/* Except in json.c, jsmn.h should only be included through this file to
 * ensure the #defines are all correct */

#define JSMN_HEADER
#ifndef JSMN_UNSIGNED
#define JSMN_UNSIGNED size_t
#endif /* JSMN_UNSIGNED */
#ifndef JSMN_SINGLE
#define JSMN_SINGLE
#endif /* JSMN_SINGLE */
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
jsmntok_t * json_lookup(const char *str, jsmntok_t *object, const char *key);

/* Move token to point at the next sibling. Does not check to see if there
 * actually is a next sibling to point to. */
void json_next(jsmntok_t **token);

/* Move a token pointing to an object key to the next key in the object.
 * Does not check to see if there actually is a next key to point to. */
void json_next_key(jsmntok_t **token);

/* Functions to convert tokens to int, double, string. Return nonzero on
 * success, zero on failure. For json_to_string(), and if return is negative
 * for json_to_string_len(), free() the string after use. */
int json_to_int(const char *str, jsmntok_t *token, int *val);
int json_to_double(const char *str, jsmntok_t *token, double *val);
/* Null-terminated */
int json_to_string(const char *str, jsmntok_t *token, char **val);
/* Not null-terminated (Will not malloc if there are not escapes) */
int json_to_string_len(const char *str, jsmntok_t *token, char **val,
        size_t *len);

#end /* JSON_H */
