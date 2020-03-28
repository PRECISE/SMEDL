#ifndef SMEDL_TYPES_H
#define SMEDL_TYPES_H

#include <pthread.h>

/*
 * SMEDL -> C type equivalencies
 *
 * int -> int
 * float -> double
 * double is alias of float
 * char -> char
 * string -> char *
 * pointer -> void *
 * thread -> pthread_t *
 * opaque -> void *
 *
 * Difference between pointer and opaque: Pointer is the pointer itself, opaque
 * is an object of unspecified structure that we have a pointer to.
 *
 * SMEDL_NULL is for a placeholder value, e.g. if only some monitor identities
 * are specified, the others will be SMEDL_NULL.
 */

typedef enum {SMEDL_INT, SMEDL_FLOAT, SMEDL_CHAR, SMEDL_STRING, SMEDL_POINTER,
    SMEDL_THREAD, SMEDL_OPAQUE, SMEDL_NULL} SMEDLType;

/*
 * A single SMEDL value
 */
typedef struct {
    SMEDLType t;
    union {
        int i;
        double d;
        char c;
        char *s;
        void *p;
        pthread_t th;
    } v;
    int reserved;  // Not currently used. Originally, the plan was to make a
                   // copy of strings so we don't have to worry about the
                   // original string being deallocated, then keep a reference
                   // count here so we can free the copy when necessary. But,
                   // that strategy won't work for opaque since we can't copy
                   // it.
} SMEDLValue;

/*
 * Auxiliary data is passed through monitors untouched. It might be used for
 * provenance info or any other attachment to events.
 */
typedef struct {
    void *data;
    size_t len;
} Aux;

#endif //SMEDL_TYPES_H
