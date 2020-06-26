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
 * str - The string containing JSON data. May be NULL if object is NULL.
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

/* Convert token to int. Returns nonzero on success, zero if:
 * - Token type is not JSMN_PRIMITIVE
 * - Token contains "null"
 * - Integer overflows (in which case INT_MIN or INT_MAX will be stored in
 *   val).
 * "true" and "false" will be converted to 1 and 0, respectively. */
int json_to_int(const char *str, jsmntok_t *token, int *val);

/* Convert token to double. Returns nonzero on success, zero if:
 * - Token type is not JSMN_PRIMITIVE
 * - Token contains "true", "false", or "null"
 * - Double overflows or underflows (in which case HUGE_VAL, 0, or -HUGE_VAL
 *   will be stored in val). */
int json_to_double(const char *str, jsmntok_t *token, double *val);

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token type is not JSMN_STRING
 * - Out-of-memory
 * Free the string after it is no longer needed. The resulting string will be
 * null-terminated. */
int json_to_string(const char *str, jsmntok_t *token, char **val);

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token type is not JSMN_STRING
 * - Out-of-memory
 * Free the string after it is no longer needed. The resulting string will be
 * null-terminated but may contain NULL. */
int json_to_opaque(const char *str, jsmntok_t *token, char **val, size_t *len);

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token is not JSMN_STRING
 * - Out-of-memory
 * If return is negative, free() the string after it is no longer needed.
 * The resulting string will not be null-terminated. If there are no escapes,
 * it will simply be a pointer to the original string in the token. */
int json_to_string_len(const char *str, jsmntok_t *token, char **val,
        size_t *len);

#end /* JSON_H */
