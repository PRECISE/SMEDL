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
 * An opaque value
 *
 * Opaque types are treated as blobs of data of unknown structure. They are
 * compared for equality by comparing the data they contain. (To compare for
 * equality by comparing their address, use the pointer type instead.)
 *
 * Opaques are hashed based on their data when used as monitor identities, so
 * when used as such, it is important to ensure their data cannot change!
 */
typedef struct {
    void *data;
    size_t size;
} SMEDLOpaque;

//TODO Should string in SMEDLValue be const char * and data in SMEDLOpaque be
// const void *?

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
        SMEDLOpaque o;
    } v;
} SMEDLValue;

/*
 * Compare two SMEDLValue and return <0 if the first is less than the second,
 * 0 if they are identical, >0 if the first is greater than the second
 */
int smedl_compare(SMEDLValue v1, SMEDLValue v2);

/*
 * Auxiliary data is passed through monitors untouched. It might be used for
 * provenance info or any other attachment to events.
 */
typedef struct {
    void *data;
    size_t len;
} SMEDLAux;

#endif /* SMEDL_TYPES_H */
