#ifndef LOCAL_WRAPPER_H
#define LOCAL_WRAPPER_H

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
    struct SMEDLRecordBase *equal; /* Linked list of matching records */
    int_fast8_t bal;
    /* The identity used as this map's key */
    SMEDLValue key;
}

/* Insertion function
 *
 * root - Pointer to root of the map to insert into
 * rec - The record to insert */
void monitor_map_insert(SMEDLRecordBase **root, SMEDLRecordBase *rec);

/* Deletion function
 *
 * root - Pointer to root of the map to delete from
 * TODO Can't simply provide a SMEDLValue to delete because need to make sure
 * it is the right record. Could provide a pointer to the record? Would that
 * require another traversal? */
void monitor_map_remove(SMEDLRecordBase **root, SMEDLRecordBase *rec);

/* Lookup function
 *
 * root - Root of the map to lookup from
 * key - Key to lookup records for
 *
 * Returns a linked list of matching records (linked with ->equal member) */
SMEDLRecordBase * monitor_map_lookup(SMEDLRecordBase *root, SMEDLValue *key);

#endif /* LOCAL_WRAPPER_H */
