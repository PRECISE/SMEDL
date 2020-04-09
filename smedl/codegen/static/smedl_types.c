#include <string.h>
#include <pthread.h>
#include "smedl_types.h"

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

/* Compare two threads
 *
 * TODO Currently this just uses compare_opaque, as pthread_t is considered an
 * opaque type by the C standard. However, this is technically undefined
 * behavior, as the only guaranteed safe way to compare threads is with
 * pthread_equal(3). This will most likely work, but if there happens to be
 * bits in a pthread_t that are ignored and arbitrary, this may not work
 * right.
 * An alternative method that would be safer would be to use something like
 * pthread_key_create(3), but that means a change to the target system. */
static int compare_thread(pthread_t t1, pthread_t t2) {
    // Only return 0 if pthread_equal(3) says they are equal
    if (pthread_equal(t1, t2)) {
        return 0;
    } else {
        if (compare_opaque(&t1, sizeof(t1), &t2, sizeof(t2)) > 0) {
            return 1;
        } else {
            return 0;
        }
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
        case SMEDL_THREAD:
            return compare_thread(v1.v.th, v2.v.th);
            break;
        case SMEDL_OPAQUE:
            return compare_opaque(v1.v.o.data, v1.v.o.size,
                    v2.v.o.data, v2.v.o.size);
            break;
        default:
            return 0; 
    }
}
