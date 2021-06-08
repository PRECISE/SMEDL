/* Monitor map implementation based on https://github.com/tidwall/hashmap.c,
 * which is available under the following open source license:
 *
 * The MIT License (MIT)
 *
 * Copyright (c) 2020 Joshua J Baker
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.*/

#ifndef MONITOR_MAP_H
#define MONITOR_MAP_H

#include <stdint.h>
#include "smedl_types.h"

/*****************************************************************************
 * Murmur hash
 *
 * Uses MurmurHash3 adapted from original by Austin Appleby
 *
 * Start with (where seed is a uint32_t):
 *   murmur_state s = MURMUR_INIT(seed)
 * Add data to the hash with:
 *   murmur(ptr, len, &s);
 * Once all data is added, get the final hash:
 *   uint64_t hash = murmur_f(&s);
 *****************************************************************************/

#define MURMUR_INIT(seed) {(uint32_t) (seed), (uint32_t) (seed), 0}

typedef struct murmur_state {
    uint64_t h1;
    uint64_t h2;
    int len;
} murmur_state;

/* Add data to hash */
void murmur(const void * key, const int len, murmur_state *s);

/* Finalize hash and get 64-bit result */
uint64_t murmur_f(murmur_state *s);

/*****************************************************************************
 * Monitor map hash tables                                                   *
 *****************************************************************************/

struct MonitorMap;

/* Single monitor record in a MonitorList. Doubly linked within the list.
 * Since most monitors will have a record in multiple monitor maps, for
 * efficient removals, this also carries a link to the monitor's
 * MonitorInstance in the next map. */
typedef struct MonitorInstance {
    struct MonitorInstance *prev;
    struct MonitorInstance *next;
    struct MonitorInstance *next_inst; /* Link to next for removal */
    struct MonitorMap *next_map;       /* Link to next map for removal */
    void *mon;
} MonitorInstance;

/* INVALID_INSTANCE is used as an error-return in local-wrappers where NULL
 * is a valid return (e.g. empty list) */
extern MonitorInstance dummy_instance;
#define INVALID_INSTANCE (&dummy_instance)

/* Stores a linked list of monitors with equivalent identities */
typedef struct MonitorList {
    uint64_t hash;
    unsigned int dib;
    MonitorInstance *head;
} MonitorList;

/* Hash table for monitor instance storage */
typedef struct MonitorMap {
    size_t capacity;    /* Current map capacity */
    size_t count;       /* Current number of MonitorMapEntries stored */
    size_t grow_at;     /* When count reaches this size, enlarge */
    size_t shrink_at;   /* When count falls to this size, shrink (min 16) */
    size_t mask;        /* Mask to convert hash->index */
    size_t offset;      /* Offset of identities array in monitor */
    uint64_t (*hash)(SMEDLValue *ids);
    int (*equals)(SMEDLValue *ids1, SMEDLValue *ids2);
    MonitorList *table;
} MonitorMap;

/* Initialize a MonitorMap. Returns nonzero if successful, zero on failure.
 *
 * Parameters:
 * map - Pointer to the MonitorMap to initialize
 * offset - Offset of identities array within the monitor struct
 * hash - Pointer to the hash function to use
 * equals - Pointer to the equality function to use */
int monitormap_init(MonitorMap *map, size_t offset,
                    uint64_t(*hash)(SMEDLValue *ids),
                    int (*equals)(SMEDLValue *ids1, SMEDLValue *ids2));

/* Insert a monitor into a MonitorMap. Returns a pointer to the MonitorInstance
 * if successful, or NULL on failure.
 *
 * Parameters:
 * map - The MonitorMap to insert into
 * mon - Pointer to the <monitor>Mon to be inserted
 * next_inst - Pointer to this monitor's instance in another MonitorMap, or
 *   NULL. (To improve removal efficiency.)
 * next_map - Pointer to the map containing next_inst */
MonitorInstance * monitormap_insert(MonitorMap *map, void *mon,
                                    MonitorInstance *next_inst,
                                    MonitorMap *next_map);

/* Fetch a list of monitors matching the identities given. If there are none,
 * return NULL.
 *
 * Parameters:
 * map - Pointer to the MonitorMap to look up in
 * ids - Array of SMEDLValues containing the identities to look up */
MonitorInstance * monitormap_lookup(MonitorMap *map, SMEDLValue *ids);

/* Remove a monitor from the MonitorMap. Recursively remove from next maps, as
 * well.
 *
 * Parameters:
 * map - The MonitorMap to insert into
 * mon - Pointer to the <monitor>Mon to be inserted */
void monitormap_remove(MonitorMap *map, void *mon);

/* Remove a MonitorInstance from the MonitorMap. Recursively remove from next
 * maps, as well.
 *
 * Parameters:
 * map - The MonitorMap to insert into
 * inst - Pointer to the MonitorInstance to be inserted */
void monitormap_removeinst(MonitorMap *map, MonitorInstance *inst);

/* Cleanup a MonitorMap. Optionally get a list of all the instances within
 * after cleaning them up from their other linked maps. Otherwise, return NULL.
 *
 * Parameters:
 * map - The MonitorMap to clean up.
 * free_contents - If true, will clean up the instances from all their linked
 *   maps and return a linked list of all instances. Each instance must be
 *   freed when no longer needed.
 */
MonitorInstance * monitormap_free(MonitorMap *map, int free_contents);

#endif /* MONITOR_MAP_H */
