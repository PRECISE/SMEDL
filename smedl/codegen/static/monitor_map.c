#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include "smedl_types.h"
#include "monitor_map.h"

/*****************************************************************************
 * Murmur hash
 * Uses MurmurHash3 adapted from original by Austin Appleby
 *****************************************************************************/

/* Add data to hash */
void murmur(const void * key, const int len, murmur_state *s) {
    const uint8_t * data = (const uint8_t*)key;
    const int nblocks = len / 16;
    uint64_t h1 = s->h1;
    uint64_t h2 = s->h2;

    const uint64_t c1 = UINT64_C(0x87c37b91114253d5);
    const uint64_t c2 = UINT64_C(0x4cf5ad432745937f);

    const uint64_t * blocks = (const uint64_t *)(data);
    for(int i = 0; i < nblocks; i++) {
        uint64_t k1 = blocks[i*2+0];
        uint64_t k2 = blocks[i*2+1];
        k1 *= c1; k1 = (k1 << 31) | (k1 >> 33);
        k1 *= c2; h1 ^= k1;
        h1 = (h1 << 27) | (h1 >> 37);
        h1 += h2; h1 = h1*5+0x52dce729;
        k2 *= c2; k2 = (k2 << 33) | (k2 >> 31);
        k2 *= c1; h2 ^= k2;
        h2 = (h2 << 31) | (h2 >> 33);
        h2 += h1; h2 = h2*5+0x38495ab5;
    }

    const uint8_t * tail = (const uint8_t*)(data + nblocks*16);
    uint64_t k1 = 0;
    uint64_t k2 = 0;
    switch(len & 15)
    {
        case 15: k2 ^= ((uint64_t)tail[14]) << 48;
        case 14: k2 ^= ((uint64_t)tail[13]) << 40;
        case 13: k2 ^= ((uint64_t)tail[12]) << 32;
        case 12: k2 ^= ((uint64_t)tail[11]) << 24;
        case 11: k2 ^= ((uint64_t)tail[10]) << 16;
        case 10: k2 ^= ((uint64_t)tail[ 9]) << 8;
        case  9: k2 ^= ((uint64_t)tail[ 8]) << 0;
                 k2 *= c2; k2 = (k2 << 33) | (k2 >> 31);
                 k2 *= c1; h2 ^= k2;

        case  8: k1 ^= ((uint64_t)tail[ 7]) << 56;
        case  7: k1 ^= ((uint64_t)tail[ 6]) << 48;
        case  6: k1 ^= ((uint64_t)tail[ 5]) << 40;
        case  5: k1 ^= ((uint64_t)tail[ 4]) << 32;
        case  4: k1 ^= ((uint64_t)tail[ 3]) << 24;
        case  3: k1 ^= ((uint64_t)tail[ 2]) << 16;
        case  2: k1 ^= ((uint64_t)tail[ 1]) << 8;
        case  1: k1 ^= ((uint64_t)tail[ 0]) << 0;
                 k1 *= c1; k1 = (k1 << 31) | (k1 >> 33);
                 k1 *= c2; h1 ^= k1;
    };

    s->h1 = h1;
    s->h2 = h2;
    s->len += len;
}

/* Finalize hash and get 64-bit result */
uint64_t murmur_f(murmur_state *s) {
    uint64_t h1 = s->h1;
    uint64_t h2 = s->h2;
    h1 ^= s->len; h2 ^= s->len;
    h1 += h2;
    h2 += h1;
    h1 ^= h1 >> 33;
    h1 *= UINT64_C(0xff51afd7ed558ccd);
    h1 ^= h1 >> 33;
    h1 *= UINT64_C(0xc4ceb9fe1a85ec53);
    h1 ^= h1 >> 33;
    h2 ^= h2 >> 33;
    h2 *= UINT64_C(0xff51afd7ed558ccd);
    h2 ^= h2 >> 33;
    h2 *= UINT64_C(0xc4ceb9fe1a85ec53);
    h2 ^= h2 >> 33;
    h1 += h2;
    h2 += h1;
    return h1;
}

/*****************************************************************************
 * Monitor map hash tables                                                   *
 *****************************************************************************/

MonitorInstance dummy_instance;

/* MIN_CAPACITY *must* be a power of 2! */
#define MIN_CAPACITY 16
#define GROW_THRESHOLD 0.75
#define SHRINK_THRESHOLD 0.1
/* Map capacity grows/shrinks by a factor of 2^GROWTH_ORDER */
#define GROWTH_ORDER 1

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

#define IDS_OF(mon) (*(SMEDLValue **) ((mon) + map->offset))

/* Initialize a MonitorMap. Returns nonzero if successful, zero on failure.
 *
 * Parameters:
 * map - Pointer to the MonitorMap to initialize
 * offset - Offset of identities array within the monitor struct
 * hash - Pointer to the hash function to use
 * equals - Pointer to the equality function to use */
int monitormap_init(MonitorMap *map, size_t offset,
                    uint64_t(*hash)(SMEDLValue *ids),
                    int (*equals)(SMEDLValue *ids1, SMEDLValue *ids2)) {
    map->capacity = MIN_CAPACITY;
    map->mask = map->capacity - 1;
    map->count = 0;
    map->grow_at = map->capacity * GROW_THRESHOLD;
    map->shrink_at = map->capacity * SHRINK_THRESHOLD;
    map->offset = offset;
    map->hash = hash;
    map->equals = equals;
    map->table = calloc(map->capacity, sizeof(MonitorList));
    if (map->table == NULL) {
        return 0;
    }
    return 1;
}

/* Grow or shrink the monitor map to the new capacity. Return nonzero if
 * successful, zero if not successful.
 *
 * Parameters:
 * map - Pointer to the MonitorMap to resize
 * capacity - New capacity. Must be a power of two!
 */
static int monitormap_resize(MonitorMap *map, size_t capacity) {
    MonitorList *new_table = calloc(capacity, sizeof(MonitorList));
    if (new_table == NULL) {
        return 0;
    }

    size_t mask = capacity - 1;

    for (size_t i = 0; i < map->capacity; i++) {
        if (map->table[i].dib == 0) {
            continue;
        }
        map->table[i].dib = 1;
        size_t j = map->table[i].hash & mask;
        while (1) {
            if (new_table[j].dib == 0) {
                new_table[j] = map->table[i];
                break;
            }
            if (new_table[j].dib < map->table[i].dib) {
                MonitorList tmp = new_table[j];
                new_table[j] = map->table[i];
                map->table[i] = tmp;
            }
            j++;
            j &= mask;
            map->table[i].dib++;
        }
    }
    free(map->table);
    map->table = new_table;
    map->capacity = capacity;
    map->mask = mask;
    map->grow_at = map->capacity * GROW_THRESHOLD;
    map->shrink_at = map->capacity * SHRINK_THRESHOLD;
    return 1;
}

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
                                    MonitorMap *next_map) {
    if (map->count == map->grow_at) {
        if (!monitormap_resize(map, map->capacity << GROWTH_ORDER)) {
            return NULL;
        }
    }

    MonitorList entry;
    entry.head = malloc(sizeof(MonitorInstance));
    if (entry.head == NULL) {
        return NULL;
    }
    entry.head->mon = mon;
    entry.head->next = NULL;
    entry.head->prev = NULL;
    entry.head->next_inst = next_inst;
    entry.head->next_map = next_map;
    entry.hash = map->hash(IDS_OF(mon));
    entry.dib = 1;
    size_t i = entry.hash & map->mask;
    MonitorInstance *retval = entry.head;

    while (1) {
        if (map->table[i].dib == 0) {
            map->table[i] = entry;
            map->count++;
            return retval;
        } else if (map->table[i].hash == entry.hash &&
                map->equals(IDS_OF(mon), IDS_OF(map->table[i].head->mon))) {
            entry.head->next = map->table[i].head;
            map->table[i].head->prev = entry.head;
            map->table[i].head = entry.head;
            return retval;
        } else if (map->table[i].dib < entry.dib) {
            MonitorList tmp = map->table[i];
            map->table[i] = entry;
            entry = tmp;
        } else {
            i++;
            i &= map->mask;
            entry.dib++;
        }
    }
}

/* Find the index in the hash table for a particular set of monitor identities.
 * If not found, return ((size_t) -1).
 *
 * Parameters:
 * map - Pointer to the MonitorMap to look up in
 * ids - Array of SMEDLValues containing the identities to look up */
static size_t monitormap_lookup_index(MonitorMap *map, SMEDLValue *ids) {
    uint64_t hash = map->hash(ids);
    size_t i = hash & map->mask;
    unsigned int dib = 1;

    while (1) {
        if (map->table[i].dib < dib) {
            return ((size_t) -1);
        }
        if (map->table[i].hash == hash &&
                map->equals(ids, IDS_OF(map->table[i].head->mon))) {
            return i;
        }
        i++;
        i &= map->mask;
        dib++;
    }
}

/* Fetch a list of monitors matching the identities given. If there are none,
 * return NULL.
 *
 * Parameters:
 * map - Pointer to the MonitorMap to look up in
 * ids - Array of SMEDLValues containing the identities to look up */
MonitorInstance * monitormap_lookup(MonitorMap *map, SMEDLValue *ids) {
    size_t i = monitormap_lookup_index(map, ids);
    if (i == (size_t) -1) {
        return NULL;
    } else {
        return map->table[i].head;
    }
}

/* Remove a MonitorInstance from the MonitorList in bucket i. Remove it from
 * the next MonitorMap as well, if there is one. Then free the MonitorInstance.
 *
 * Parameters:
 * map - Pointer to the MonitorMap being removed from
 * inst - MonitorInstance to remove
 * i - Bucket of the MonitorList to remove from
 */
static void monitormap_remove_from_list(MonitorMap *map, MonitorInstance *inst,
                                        size_t i) {
    if (inst->prev != NULL) {
        inst->prev->next = inst->next;
    } else {
        map->table[i].head = inst->next;
    }
    if (inst->next != NULL) {
        inst->next->prev = inst->prev;
    }

    if (inst->next_map != NULL) {
        monitormap_removeinst(inst->next_map, inst->next_inst);
    }
    free(inst);
}

/* Remove the MonitorList in bucket i from the map.
 *
 * Parameters:
 * map - Pointer to the MonitorMap being removed from
 * i - Bucket of the MonitorList to remove */
static void monitormap_remove_list(MonitorMap *map, size_t i) {
    map->table[i].dib = 0;
    while (1) {
        size_t prev_i = i;
        i++;
        i &= map->mask;
        if (map->table[i].dib <= 1) {
            map->table[prev_i].dib = 0;
            break;
        }
        map->table[prev_i] = map->table[i];
        map->table[prev_i].dib--;
    }
    map->count--;
    if (map->capacity > MIN_CAPACITY && map->count <= map->shrink_at) {
        // Failure to shrink won't cause problems except extra memory usage
        monitormap_resize(map, map->capacity >> 2);
    }
}

/* Remove a MonitorInstance from the MonitorMap. Recursively remove from next
 * maps, as well.
 *
 * Parameters:
 * map - The MonitorMap to insert into
 * inst - Pointer to the MonitorInstance to be inserted */
void monitormap_removeinst(MonitorMap *map, MonitorInstance *inst) {
    size_t i = monitormap_lookup_index(map, IDS_OF(inst->mon));
    assert(i != (size_t) -1);   // Not found
    monitormap_remove_from_list(map, inst, i);

    /* If it was the last monitor in the list, remove this list from the hash
     * table. */
    if (map->table[i].head == NULL) {
        monitormap_remove_list(map, i);
    }
}

/* Remove a monitor from the MonitorMap. Recursively remove from next maps, as
 * well.
 *
 * Parameters:
 * map - The MonitorMap to insert into
 * mon - Pointer to the <monitor>Mon to be inserted */
void monitormap_remove(MonitorMap *map, void *mon) {
    size_t i = monitormap_lookup_index(map, IDS_OF(mon));
    assert(i != (size_t) -1);   // Not found

    /* Find the MonitorInstance and remove from its list */
    MonitorInstance *curr = map->table[i].head;
    for (; curr != NULL && curr->mon != mon; curr = curr->next);
    assert(curr != NULL);   // Not found
    monitormap_remove_from_list(map, curr, i);

    /* If it was the last monitor in the list, remove this list from the hash
     * table. */
    if (map->table[i].head == NULL) {
        monitormap_remove_list(map, i);
    }
}

/* Cleanup a MonitorMap. Optionally get a list of all the instances within
 * after cleaning them up from their other linked maps. Otherwise, return NULL.
 *
 * Parameters:
 * map - The MonitorMap to clean up.
 * free_contents - If true, will clean up the instances from all their linked
 *   maps and return a linked list of all instances. Each instance must be
 *   freed when no longer needed.
 */
MonitorInstance * monitormap_free(MonitorMap *map, int free_contents) {
    MonitorInstance *result = NULL;
    if (free_contents) {
        for (size_t i = 0; i < map->capacity; i++) {
            if (map->table[i].dib > 0) {
                MonitorInstance *inst = map->table[i].head;
                while (inst != NULL) {
                    if (inst->next_map != NULL) {
                        monitormap_removeinst(inst->next_map, inst);
                    }
                    MonitorInstance *tmp = inst->next;
                    inst->next = result;
                    result = inst;
                    inst = tmp;
                }
            }
        }
    }
    free(map->table);
    return result;
}
