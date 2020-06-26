#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <errno.h>
#ifdef DEBUG
#include <stdio.h>
#endif /* DEBUG */

#ifndef JSMN_UNSIGNED
#define JSMN_UNSIGNED size_t
#endif /* JSMN_UNSIGNED */
#ifndef JSMN_SINGLE
#define JSMN_SINGLE
#endif /* JSMN_SINGLE */
#include "jsmn.h"

/* Must come after the jsmn #include and #defines above */
#include "json.h"

/* Lookup a key and return a pointer to the value token. This is most efficient
 * when looking up keys from the same object and in the order in which they
 * appear in the object. Return NULL if the provided token is not an object or
 * the key is not found.
 *
 * Parameters:
 * str - The string containing JSON data. May be NULL if object is NULL.
 * object - A pointer to the object token. For efficient lookups, use NULL to
 *   look up from the same object in subsequent calls.
 * key - The key to look up
 */
jsmntok_t * json_lookup(const char *str, jsmntok_t *object, const char *key) {
    static const char *string;
    static jsmntok_t *start;
    static jsmntok_t *curr;
    static size_t index, size;

    /* If object was provided, reset everything */
    if (object != NULL) {
        if (object->type != JSMN_OBJECT) {
#ifdef DEBUG
            fprintf(stderr, "Called json_lookup on a non-object token\n");
#endif /* DEBUG */
            return NULL;
        }
        string = str;
        start = object;
        curr = object;
        index = 0;
        /* Size is number of key/value pairs */
        size = object->size;
    }

    /* Search for the key */
    int i = index;
    int result;
    char *curr_key;
    size_t curr_len;
    do {
        result = json_to_string_len(string, curr, &curr_key, &curr_len);
        if (!result) {
#ifdef DEBUG
            fprintf(stderr, "Could not un-escape string token\n");
#endif /* DEBUG */
            return NULL;
        }
        if (strlen(key) == curr_len && /* Don't match "foo" with "foobar" */
                !strncmp(key, curr_key, curr_len)) {
            /* Found it */
            index = i + 1;
            jsmntok_t *val = curr + 1;
            json_next_key(&curr);
            if (index == size) {
                index = 0;
                curr = start;
            }
            return val;
        }
        if (result < 0) {
            free(curr_key);
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
    for (size_t remaining = 1; remaining > 0; remaining--) {
        /* size is number of key-value pairs for objects, number of elements
         * for arrays, 1 for the key in a key-value pair, 0 otherwise */
        remaining += (*token)->size;
        (*token)++;
    }
}

/* Move a token pointing to an object key to the next key in the object.
 * Does not check to see if there actually is a next key to point to. */
void json_next_key(jsmntok_t **token) {
    /* Advance past key */
    (*token)++;
    /* Advance past value */
    json_next(token);
}

/* Convert token to int. Returns nonzero on success, zero if:
 * - Token type is not JSMN_PRIMITIVE
 * - Token contains "null"
 * - Integer overflows (in which case INT_MIN or INT_MAX will be stored in
 *   val).
 * "true" and "false" will be converted to 1 and 0, respectively. */
int json_to_int(const char *str, jsmntok_t *token, int *val) {
    /* Check if a non-primitive, true, false, or null */
    if (token->type != JSMN_PRIMITIVE) {
#ifdef DEBUG
        fprintf(stderr, "Called json_to_int on a non-primitive token\n");
#endif /* DEBUG */
        return 0;
    } else if (str[token->start] == 'n') {
#ifdef DEBUG
        fprintf(stderr, "Called json_to_int on 'null'\n");
#endif /* DEBUG */
        return 0;
    } else if (str[token->start] == 't') {
        *val = 1;
        return 1;
    } else if (str[token->start] == 'f') {
        *val = 0;
        return 1;
    }

    /* strtol stops when it finds \0 or some other char that can't be part of
     * the number */
    long int tmp = strtol(str + token->start, NULL, 10);
    if (tmp < INT_MIN) {
        *val = INT_MIN;
        return 0;
    } else if (tmp > INT_MAX) {
        *val = INT_MAX;
        return 0;
    }
    *val = tmp;
    return 1;
}

/* Convert token to double. Returns nonzero on success, zero if:
 * - Token type is not JSMN_PRIMITIVE
 * - Token contains "true", "false", or "null"
 * - Double overflows or underflows (in which case HUGE_VAL, 0, or -HUGE_VAL
 *   will be stored in val). */
int json_to_double(const char *str, jsmntok_t *token, double *val) {
    /* Check if a non-primitive, true, false, or null */
    if (token->type != JSMN_PRIMITIVE) {
#ifdef DEBUG
        fprintf(stderr, "Called json_to_double on a non-primitive token\n");
#endif /* DEBUG */
        return 0;
    } else if (str[token->start] == 'n' ||
            str[token->start] == 't' ||
            str[token->start] == 'f') {
#ifdef DEBUG
        fprintf(stderr, "Called json_to_int on 'true'/'false'/'null'\n");
#endif /* DEBUG */
        return 0;
    }

    errno = 0;
    /* strtod stops when it finds \0 or some other char that can't be part of
     * the number */
    *val = strtod(str + token->start, NULL);
    if (errno == ERANGE) {
        return 0;
    }
    return 1;
}

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token type is not JSMN_STRING
 * - Out-of-memory
 * Free the string after it is no longer needed. The resulting string will be
 * null-terminated. */
int json_to_string(const char *str, jsmntok_t *token, char **val) {
    size_t len;
    int result = json_to_string_len(str, token, val, &len);
    if (result == 0) {
        return 0;
    } else if (result > 0) {
        char *tmp = *val;
        *val = malloc(len + 1);
        if (*val == NULL) {
            return 0;
        }
        memcpy(*val, tmp, len);
    }

    /* Relies on the fact that json_to_string_len only mallocs the string
     * when there is an escape sequence that was removed, meaning there is
     * at least one byte of extra space allocated */
    (*val)[len] = '\0';
    return 1;
}

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token type is not JSMN_STRING
 * - Out-of-memory
 * Free the string after it is no longer needed. The resulting string will not
 * be null-terminated but will always be malloc'd. */
int json_to_opaque(const char *str, jsmntok_t *token, char **val, size_t *len) {
    int result = json_to_string_len(str, token, val, len);
    if (result == 0) {
        return 0;
    } else if (result > 0) {
        char *tmp = *val;
        *val = malloc(*len);
        if (*val == NULL) {
            return 0;
        }
        memcpy(*val, tmp, *len);
    }
    return 1;
}

/* Take a Unicode escape from the source str, encode it in UTF-8, and append it
 * to the result str.
 *
 * result - Result string
 * str - Source string
 * res_copied - Index to append at in the result string. Will be updated to
 *   the index of the new end of the string.
 * i - Index to read from in the source string. Will be updated to the index of
 *   the last character read. */
static void unescape_unicode(char *result, const char *str,
        size_t *res_copied, size_t *i) {
    /* Convert hex to int */
    size_t j;
    uint32_t codepoint = 0;
    for (j = *i; j < *i + 4; j++) {
        codepoint <<= 4;
        if ('0' <= str[j] && str[j] <= '9') {
            codepoint += str[j] - '0';
        } else if ('A' <= str[j] && str[j] <= 'F') {
            codepoint += str[j] - 'A' + 10;
        } else {
            codepoint += str[j] - 'a' + 10;
        }
    }

    if (0xd800 <= codepoint && codepoint < 0xdc00) {
        /* This codepoint was a high surrogate. There should be a low surrogate
         * following (but may not be if not well-formed Unicode). If so,
         * update the codepoint accordingly. */
        if (str[j] == '\\' && str[j + 1] == 'u') {
            uint32_t low_surr = 0;
            for (j += 2; j < *i + 10; j++) {
                low_surr <<= 4;
                if ('0' <= str[j] && str[j] <= '9') {
                    low_surr += str[j] - '0';
                } else if ('A' <= str[j] && str[j] <= 'F') {
                    low_surr += str[j] - 'A' + 10;
                } else {
                    low_surr += str[j] - 'a' + 10;
                }
            }
            codepoint = (codepoint & 0x3ff) << 10 | (low_surr & 0x3ff);
        }
    }

    /* Append to result */
    if (codepoint < 0x80) {
        result[*res_copied] = codepoint;
        *res_copied += 1;
    } else if (codepoint < 0x800) {
        result[*res_copied] = 0xc0 | (codepoint >> 6);
        result[*res_copied + 1] = 0x80 | (codepoint & 0x3f);
        *res_copied += 2;
    } else if (codepoint < 0x10000) {
        result[*res_copied] = 0xe0 | (codepoint >> 12);
        result[*res_copied + 1] = 0x80 | ((codepoint >> 6) & 0x3f);
        result[*res_copied + 2] = 0x80 | (codepoint & 0x3f);
        *res_copied += 3;
    } else {
        result[*res_copied] = 0xf0 | (codepoint >> 18);
        result[*res_copied + 1] = 0x80 | ((codepoint >> 12) & 0x3f);
        result[*res_copied + 2] = 0x80 | ((codepoint >> 6) & 0x3f);
        result[*res_copied + 3] = 0x80 | (codepoint & 0x3f);
        *res_copied += 4;
    }

    *i = j - 1;
    return;
}

/* Convert token to string. Returns nonzero on success, zero if:
 * - Token is not JSMN_STRING
 * - Out-of-memory
 * If return is negative, free() the string after it is no longer needed.
 * The resulting string will not be null-terminated. If there are no escapes,
 * it will simply be a pointer to the original string in the token. */
int json_to_string_len(const char *str, jsmntok_t *token, char **val,
    size_t *len) {
    /* Check if a non-string */
    if (token->type != JSMN_STRING) {
#ifdef DEBUG
        fprintf(stderr, "Called json_to_string(_len) on a non-string token\n");
#endif /* DEBUG */
        return 0;
    }

    char *result = NULL;
    size_t res_copied = 0, str_copied = 0;
    str += token->start
    size_t tok_len = token->end - token->start;
    for (size_t i = 0; i < tok_len; i++) {
        if (str[i] == '\\') {
            if (result == NULL) {
                result = malloc(tok_len);
                if (result == NULL) {
                    return 0;
                }
            }
            memcpy(result + res_copied, str + str_copied, i - str_copied);
            res_copied += i - str_copied;
            i++;
            switch (str[i]) {
                case '\\':
                case '\"':
                case '/':
                    result[res_copied] = str[i];
                    res_copied++;
                    str_copied = i + 1;
                    break;
                case 'b':
                    result[res_copied] = '\b';
                    res_copied++;
                    str_copied = i + 1;
                    break;
                case 'f':
                    result[res_copied] = '\f';
                    res_copied++;
                    str_copied = i + 1;
                    break;
                case 'n':
                    result[res_copied] = '\n';
                    res_copied++;
str_copied = i + 1;
                    break;
                case 'r':
                    result[res_copied] = '\r';
                    res_copied++;
                    str_copied = i + 1;
                    break;
                case 't':
                    result[res_copied] = '\t';
                    res_copied++;
                    str_copied = i + 1;
                    break;
                case 'u':
                    i++;
                    unescape_unicode(result, str, &res_copied, &i);
                    str_copied = i + 1;
                    break;
            }
        }
    }

    if (result != NULL) {
        memcpy(result + res_copied, str + str_copied, tok_len - str_copied);
        res_copied += tok_len - str_copied;
        *len = res_copied;
        *val = result;
    } else {
        *len = tok_len;
        *val = str;
    }
    return 1;
}
