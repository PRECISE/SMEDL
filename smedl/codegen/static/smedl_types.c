#include <string.h>
#include <pthread.h>
#include "smedl_types.h"

/* 
 * Compare two SMEDLOpaque values and return nonzero if they are equal, zero if
 * not 
 */
int opaque_equal(SMEDLOpaque o1, SMEDLOpaque o2) {
    return o1.size == o2.size && !memcmp(o1.data, o2.data, o1.size);
}

/*
 * Compute the hash of arbitrary data as a CRC-32
 */
static unsigned int hash_opaque(void *data, size_t size) {
    // Use a lookup table for speed, generated the first time this function runs
    static int table_ready = 0;
    static uint32_t table[256];
    if (!table_ready) {
        for (int i = 0; i < 256; i++) {
            uint32_t remainder = i;
            for (int j = 0; j < 8; j++) {
                if (remainder & 1) {
                    remainder >>= 1;
                    remainder ^= 0xedb88320;
                } else {
                    remainder >>= 1;
                }
            }
            table[i] = remainder;
        }
        table_ready = 1;
    }

    // Calculate CRC
    uint32_t crc = 0xffffffff;
    for (size_t i = 0; i < size; i++) {
        crc = (crc >> 8) ^ table[(crc ^ data[i]) & 0xff];
    }
    return ~crc;
}

/*
 * Compute a hash of a pthread_t
 */
static unsigned int hash_pthread_t(pthread_t th) {
    //TODO This will probably work, generally, but is unportable. Consider
    // another solution, such as using pthread_key_create(3) (maybe with an mgen
    // command line flag to fall back to this)
    return hash_opaque(&th, sizeof(th));
}

/*
 * Compute a hash of the SMEDLValue useful for hash tables
 */
unsigned int smedl_hash(SMEDLValue val) {
    switch (val.t) {
        case SMEDL_INT:
            return val.v.i;
            break;
        case SMEDL_FLOAT:
            return 0; //TODO find a hash function of some sort where if
                      // C == is true, the hashes are also equal
            break;
        case SMEDL_CHAR:
            return val.v.c;
            break;
        case SMEDL_STRING:
            // djb2 from http://www.cse.yorku.ca/~oz/hash.html
            {
                unsigned char *str = val.v.s;
                unsigned long int acc = 5381;
                uint_fast8_t c;
                while (c = *str++) {
                    acc = ((acc << 5) + acc) ^ c;
                }
                return acc;
            }
            break;
        case SMEDL_POINTER:
            // uintptr_t is an unsigned int that a void * can safely convert
            // to and from. (This will likely be truncated further by the
            // unsigned int conversion when returning.)
            return (uintptr_t) val.v.o;
            break;
        case SMEDL_THREAD:
            return hash_pthread_t(val.v.th);
            break;
        case SMEDL_OPAQUE:
            return hash_opaque(val.v.o.data, val.v.o.size);
            break;
        default:
            return 0; 
    }
}
