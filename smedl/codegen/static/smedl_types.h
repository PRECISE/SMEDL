#ifndef SMEDL_TYPES_H
#define SMEDL_TYPES_H

#include <string.h>
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

/* Compare two opaque values for equality only. Return nonzero if equal, zero
 * if not */
int opaque_equals(SMEDLOpaque o1, SMEDLOpaque o2);

/* Make a copy of the src string in dest (does not free the old value!) */
int smedl_assign_string(char **dest, char *src);

/* Make a copy of the src opaque in dest (does not free the old value!) */
int smedl_assign_opaque(SMEDLOpaque *dest, SMEDLOpaque src);

/* Free the old dest and make a copy of the src string in dest */
int smedl_replace_string(char **dest, char *src);

/* Free the old dest and make a copy of the src opaque in dest */
int smedl_replace_opaque(SMEDLOpaque *dest, SMEDLOpaque src);

/*
 * Compare two SMEDLValue and return <0 if the first is less than the second,
 * 0 if they are identical, >0 if the first is greater than the second
 *
 * NOTE: No type checking is performed! Results are undefined if v1 and v2 are
 * not the same type!
 */
int smedl_compare(SMEDLValue v1, SMEDLValue v2);

/*
 * Compare two SMEDLValue and return nonzero if they are equal, zero if they are
 * not. If the first value is a wildcard (represented by type being SMEDL_NULL),
 * the result is always a match.
 *
 * NOTE: No type checking is performed! Results are undefined if v1 and v2 are
 * not the same type (excluding SMEDL_NULL for a wildcard first value)!
 */
int smedl_equal(SMEDLValue v1, SMEDLValue v2);

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
int smedl_equal_array(SMEDLValue *a1, SMEDLValue *a2, size_t len);

/* 
 * Make a copy of the SMEDLValue array with the given length. This is a deep
 * copy: new buffers will be malloc'd for strings and opaques.
 *
 * Return the copy, or NULL if it could not be made.
 */
SMEDLValue * smedl_copy_array(SMEDLValue *array, size_t len);

/*
 * Free the array of SMEDLValue and any strings and opaques it contains
 */
void smedl_free_array(SMEDLValue *array, size_t len);

/*
 * A callback function pointer for receiving exported events from monitors and
 * global wrappers
 */
typedef void (*SMEDLCallback)(SMEDLValue *identities, SMEDLValue *params,
        void *aux);

#endif /* SMEDL_TYPES_H */
