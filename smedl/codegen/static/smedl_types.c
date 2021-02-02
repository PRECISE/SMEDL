#include <stdlib.h>
#include <stdint.h>
/* stdio.h, inttypes.h, and errno.h only needed for pointer conversion */
#include <stdio.h>
#include <inttypes.h>
#include <errno.h>
#include <string.h>
#include "smedl_types.h"

/* Compare two opaque values for equality only. Return nonzero if equal, zero
 * if not */
int smedl_opaque_equals(SMEDLOpaque o1, SMEDLOpaque o2) {
    return o1.size == o2.size && !memcmp(o1.data, o2.data, o1.size);
}

/* Compare two opaque values */
static int compare_opaque(void *data1, size_t len1, void *data2, size_t len2) {
    size_t i = 0;
    while (1) {
        if (i == len1) {
            if (i == len2) {
                return 0;
            } else {
                return -1;
            }
        } else if (i == len2) {
            return 1;
        }

        if (*((unsigned char *) data1) < *((unsigned char *) data2)) {
            return -1;
        } else if (*((unsigned char *) data1) > *((unsigned char *) data2)) {
            return 1;
        }

        i++;
    }
}

/*
 * Compare two SMEDLValue and return <0 if the first is less than the second,
 * 0 if they are identical, >0 if the first is greater than the second
 *
 * NOTE: No type checking is performed! Results are undefined if v1 and v2 are
 * not the same type!
 */
int smedl_compare(SMEDLValue v1, SMEDLValue v2) {
    switch (v1.t) {
        case SMEDL_INT:
            if (v1.v.i < v2.v.i) {
                return -1;
            } else if (v1.v.i > v2.v.i) {
                return 1;
            } else {
                return 0;
            }
            break;
        case SMEDL_FLOAT:
            if (v1.v.d < v2.v.d) {
                return -1;
            } else if (v1.v.d > v2.v.d) {
                return 1;
            } else {
                return 0;
            }
            break;
        case SMEDL_CHAR:
            if (v1.v.c < v2.v.c) {
                return -1;
            } else if (v1.v.c > v2.v.c) {
                return 1;
            } else {
                return 0;
            }
            break;
        case SMEDL_STRING:
            return strcmp(v1.v.s, v2.v.s);
            break;
        case SMEDL_POINTER:
            if ((uintptr_t) v1.v.p < (uintptr_t) v2.v.p) {
                return -1;
            } else if ((uintptr_t) v1.v.p > (uintptr_t) v2.v.p) {
                return 1;
            } else {
                return 0;
            }
            break;
        case SMEDL_OPAQUE:
            return compare_opaque(v1.v.o.data, v1.v.o.size,
                    v2.v.o.data, v2.v.o.size);
            break;
        default:
            return 0;
    }
}

/*
 * Compare two SMEDLValue and return nonzero if they are equal, zero if they are
 * not. If the first value is a wildcard (represented by type being SMEDL_NULL),
 * the result is always a match.
 *
 * NOTE: No type checking is performed! Results are undefined if v1 and v2 are
 * not the same type (excluding SMEDL_NULL for a wildcard first value)!
 */
int smedl_equal(SMEDLValue v1, SMEDLValue v2) {
    switch (v1.t) {
        case SMEDL_INT:
            return v1.v.i == v2.v.i;
        case SMEDL_FLOAT:
            return v1.v.d == v2.v.d;
        case SMEDL_CHAR:
            return v1.v.c == v2.v.c;
        case SMEDL_STRING:
            return strcmp(v1.v.s, v2.v.s) == 0;
        case SMEDL_POINTER:
            return v1.v.p == v2.v.p;
        case SMEDL_OPAQUE:
            return smedl_opaque_equals(v1.v.o, v2.v.o);
        case SMEDL_NULL:
            return 1;
        default:
            return 0;
    }
}

/*
 * Compare two arrays of SMEDLValue and return nonzero if each element in the
 * first is equal to the corresponding element in the second. The first array
 * may contain wildcards (represented by type being SMEDL_NULL), which will
 * always match.
 *
 * NOTE: No type checking is performed! Results are undefined if any of the
 * corresponding elements are not of the same type (excluding SMEDL_NULL for
 * wildcards in the first array)!
 */
int smedl_equal_array(SMEDLValue *a1, SMEDLValue *a2, size_t len) {
    for (size_t i = 0; i < len; i++) {
        if (!smedl_equal(a1[i], a2[i])) {
            return 0;
        }
    }
    return 1;
}

/* Make a copy of the src string in dest (does not free the old value!)
 * Return nonzero on success, zero on failure */
int smedl_assign_string(char **dest, char *src) {
    char *tmp = malloc(strlen(src) + 1);
    if (tmp == NULL) {
        return 0;
    }
    *dest = tmp;
    strcpy(*dest, src);
    return 1;
}

/* Make a copy of the src opaque in dest (does not free the old value!)
 * Return nonzero on success, zero on failure */
int smedl_assign_opaque(SMEDLOpaque *dest, SMEDLOpaque src) {
    void *tmp = malloc(src.size);
    //TODO Can return NULL correctly if size is zero
    if (tmp == NULL) {
        return 0;
    }
    (*dest).data = tmp;
    (*dest).size = src.size;
    memcpy((*dest).data, src.data, src.size);
    return 1;
}

/* Free the old dest and make a copy of the src string in dest
 * Return nonzero on success, zero on failure */
int smedl_replace_string(char **dest, char *src) {
    char *tmp = malloc(strlen(src) + 1);
    if (tmp == NULL) {
        return 0;
    }
    free(*dest);
    *dest = tmp;
    strcpy(*dest, src);
    return 1;
}

/* Free the old dest and make a copy of the src opaque in dest
 * Return nonzero on success, zero on failure */
int smedl_replace_opaque(SMEDLOpaque *dest, SMEDLOpaque src) {
    void *tmp = malloc(src.size);
    //TODO Can return NULL correctly if size is zero
    if (tmp == NULL) {
        return 0;
    }
    free((*dest).data);
    (*dest).data = tmp;
    (*dest).size = src.size;
    memcpy((*dest).data, src.data, src.size);
    return 1;
}

/*
 * Make a copy of the SMEDLValue array with the given length. This is a deep
 * copy: new buffers will be malloc'd for strings and opaques.
 *
 * Return the copy, or NULL if it could not be made.
 */
SMEDLValue * smedl_copy_array(SMEDLValue *array, size_t len) {
    SMEDLValue *copy = malloc(sizeof(SMEDLValue) * len);
    if (copy == NULL) {
        return NULL;
    }

    for (size_t i = 0; i < len; i++) {
        copy[i] = array[i];
        if (copy[i].t == SMEDL_STRING) {
            copy[i].v.s = malloc(strlen(array[i].v.s + 1));
            if (copy[i].v.s == NULL) {
                smedl_free_array(copy, i);
                return NULL;
            }
            strcpy(copy[i].v.s, array[i].v.s);
        } else if (copy[i].t == SMEDL_OPAQUE) {
            copy[i].v.o.data = malloc(array[i].v.o.size);
            if (copy[i].v.o.data == NULL) {
                smedl_free_array(copy, i);
                return NULL;
            }
            memcpy(copy[i].v.o.data, array[i].v.o.data, array[i].v.o.size);
        }
    }
    return copy;
}

/*
 * Free the array of SMEDLValue and any strings and opaques it contains.
 * This works without knowing the types beforehand, but if the types are known,
 * freeing the strings and opaque data individually and then free(array) will
 * be more efficient.
 */
void smedl_free_array(SMEDLValue *array, size_t len) {
    smedl_free_array_contents(array, len);
    free(array);
}

/*
 * Free just the strings and opaques contained in a SMEDLValue array. See note
 * for smedl_free_array() above.
 */
void smedl_free_array_contents(SMEDLValue *array, size_t len) {
    for (size_t i = 0; i < len; i++) {
        if (array[i].t == SMEDL_STRING) {
            free(array[i].v.s);
        } else if (array[i].t == SMEDL_OPAQUE) {
            free(array[i].v.o.data);
        }
    }
}

/*
 * Convert a pointer to string representation. Return nonzero on success, zero
 * on failure.
 *
 * Will only write up to size bytes to str, including the null byte.
 */
int smedl_pointer_to_string(void *ptr, char *str, size_t size) {
    int status = snprintf(str, size, "%" PRIxPTR, (uintptr_t) ptr);
    if (status < 0 || status >= size) {
        return 0;
    }
    return 1;
}

/*
 * Convert a string representation of a pointer back to a pointer. Return
 * nonzero on success, zero on failure.
 */
int smedl_string_to_pointer(const char *str, void **ptr) {
    char *endptr;
    errno = 0;
    uintptr_t ptr_int = strtol(str, &endptr, 16);
    if (errno || str[0] == '\0' || *endptr != '\0') {
        return 0;
    }
    *ptr = (void *) ptr_int;
    return 1;
}
