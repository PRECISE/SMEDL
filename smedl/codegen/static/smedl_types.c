#include <string.h>
#include "smedl_types.h"

/* 
 * Compare two SMEDLOpaque values and return nonzero if they are equal, zero if
 * not 
 */
int opaque_equal(SMEDLOpaque o1, SMEDLOpaque o2) {
    return o1.size == o2.size && !memcmp(o1.data, o2.data, o1.size);
}

/*
 * Compute a hash of the SMEDLValue useful for hash tables
 */
int smedl_hash(SMEDLValue val) {
    //TODO
}
