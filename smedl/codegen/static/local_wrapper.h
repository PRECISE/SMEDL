#ifndef LOCAL_WRAPPER_H
#define LOCAL_WRAPPER_H

#include <stdint.h>
#include "smedl_types.h"

/******************************************************************************
 * Monitor map support functions                                              *
 *                                                                            *
 * Each <monitor-name>Record type should "inherit from" SMEDLRecordBase by    *
 * using "SMEDLRecordBase r" as its first member. Then, the "monitor_map_*"   *
 * functions can be used for insertions, deletions, etc. by casting any       *
 * <monitor-name>Record pointers to SMEDLRecordBase when passing to the       *
 * functions in this header.                                                  *
 ******************************************************************************/

/* Base type for monitor map records. Actual monitor map records should
 * "subclass" this by making their first member be "SMEDLRecordBase r". */
typedef struct SMEDLRecordBase {
    /* For linked list use (function return values) */
    struct SMEDLRecordBase *next;
    /* For AVL tree use (storage in maps) */
    struct SMEDLRecordBase *parent;
    struct SMEDLRecordBase *left;
    struct SMEDLRecordBase *right;
    int_fast8_t bal;
    struct SMEDLRecordBase *equal; /* Linked list of equal records.
                                    * Only first record in the list will have
                                    * non-NULL for parent, left, or right. */
    struct SMEDLRecordBase *equal_prev;
    /* The identity used as this map's key */
    SMEDLValue key;
} SMEDLRecordBase;

/* Insertion function
 *
 * root - Pointer to root of the map to insert into
 * rec - The record to insert */
void monitor_map_insert(SMEDLRecordBase **root, SMEDLRecordBase *rec);

/* Deletion function
 *
 * rec - Record to remove from its map
 *
 * Returns the root of the updated tree. NOTE: Does not free any memory used
 * by the record. */
SMEDLRecordBase * monitor_map_remove(SMEDLRecordBase *rec);

/* Lookup function
 *
 * root - Root of the map to lookup from
 * key - Key to lookup records for
 *
 * Returns a linked list of matching records (linked with ->equal member),
 * or NULL if there were no matches. */
SMEDLRecordBase * monitor_map_lookup(SMEDLRecordBase *root, SMEDLValue key);

/* Fetch all monitors
 *
 * Return a linked list of all monitors in the map (linked with ->next
 * member) */
SMEDLRecordBase * monitor_map_all(SMEDLRecordBase *root);

#endif /* LOCAL_WRAPPER_H */
