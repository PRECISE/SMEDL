#include "smedl_types.h"
#include "local_wrapper.h"

/* BST right rotate operation */
static void right_rotate(SMEDLRecordBase **node) {
    SMEDLRecordBase *tmp = (*node)->left;
    (*node)->left = tmp->right;
    tmp->right = (*node);
    tmp->parent = (*node)->parent;
    (*node)->parent = tmp;
    *node = tmp;
}

/* BST left rotate operation */
static void left_rotate(SMEDLRecordBase **node) {
    SMEDLRecordBase *tmp = (*node)->right;
    (*node)->right = tmp->left;
    tmp->left = (*node);
    tmp->parent = (*node)->parent;
    (*node)->parent = tmp;
    *node = tmp;
}

/* Insertion function
 *
 * root - Pointer to root of the map to insert into
 * rec - The record to insert */
void monitor_map_insert(SMEDLRecordBase **root, SMEDLRecordBase *rec) {
    rec->left = NULL;
    rec->right = NULL;
    rec->bal = 0;

    /* Check for empty tree */
    if (*root == NULL) {
        rec->equal = NULL;
        rec->equal_prev = NULL;
        rec->parent = NULL;
        *root = rec;
    }

    /* Traverse the tree */
    int cmp;
    int bal_change;
    SMEDLRecordBase *node = *root;
    while (!(cmp = smedl_compare(rec->key, node->key))) {
        if (cmp < 0) {
            if (node->left == NULL) {
                /* Reached a leaf, insert on left */
                node->left = rec;
                rec->parent = node;
                rec->equal = NULL;
                rec->equal_prev = NULL;
                bal_change = -1;
            } else {
                /* Traverse left */
                node = node->left;
                continue;
            }
        } else {
            if (node->right == NULL) {
                /* Key not found, insert on right */
                node->right = rec;
                rec->parent = node;
                rec->equal = NULL;
                rec->equal_prev = NULL;
                bal_change = 1;
            } else {
                /* Traverse right */
                node = node->right;
                continue;
            }
        }

        /* Node was inserted. Check the balance. */
        do {
            node->bal += bal_change;

            /* Do rotations or prepare parent's balance correction if
             * necessary */
            switch (node->bal) {
                case -1:
                case 1:
                    /* Height of this branch grew. Figure out which child we are
                     * and update bal_change. */
                    if (node->parent == NULL) {
                        /* At the root. Nothing else to do. */
                        *root = node;
                        return;
                    } else if (node == node->parent->left) {
                        bal_change = -1;
                    } else {
                        bal_change = 1;
                    }
                    node = node->parent;
                    break;
                case -2:
                    /* Needs rebalance to the right */
                    if (node->left->bal < 0) {
                        /* Left-left case */
                        node->bal = 0;
                        right_rotate(&node);
                        node->bal = 0;
                    } else {
                        /* Left-right case */
                        left_rotate(&node->left);
                        right_rotate(&node);
                        if (node->bal < 0) {
                            node->left->bal = 0;
                            node->right->bal = 1;
                        } else if (node->bal > 0) {
                            node->left->bal = -1;
                            node->right->bal = 0;
                        } else {
                            node->left->bal = 0;
                            node->right->bal = 0;
                        }
                        node->bal = 0;
                    }
                    break;
                case 2:
                    /* Needs rebalance to the left */
                    if (node->right->bal > 0) {
                        /* Right-right case */
                        node->bal = 0;
                        left_rotate(&node);
                        node->bal = 0;
                    } else {
                        /* Right-left case */
                        right_rotate(&node->right);
                        left_rotate(&node);
                        if (node->bal < 0) {
                            node->left->bal = 0;
                            node->right->bal = 1;
                        } else if (node->bal > 0) {
                            node->left->bal = -1;
                            node->right->bal = 0;
                        } else {
                            node->left->bal = 0;
                            node->right->bal = 0;
                        }
                        node->bal = 0;
                    }
                    break;
            }
        /* If the current node's balance is zero, the height of its branch did
         * not change. Balance correction is complete. */
        } while (node->bal != 0);
        
        /* The root can only change from a rotation. If the current node has
         * no parent, a rotation may have changed the root. Update it to
         * the current node. */
        if (node->parent == NULL) {
            *root = node;
        }

        /* Insert is done, tree is balanced, and root is updated if necessary.
         * We are done. */
        return;
    }

    /* Found a matching key already present. Add to that key. */
    rec->parent = NULL;
    if (node->equal != NULL) {
        node->equal->equal_prev = rec;
    }
    rec->equal = node->equal;
    rec->equal_prev = node;
    node->equal = rec;
}

/* Swap the two records' location in the tree */
static void swap_records(SMEDLRecordBase *a, SMEDLRecordBase *b) {
    SMEDLRecordBase tmp = *a;

    /* Put b in a's spot */
    if (a->parent != NULL && a->parent->left == a) {
        a->parent->left = b;
    } else if (a->parent != NULL) {
        a->parent->right = b;
    }
    if (a->left != NULL) {
        a->left->parent = b;
    }
    if (a->right != NULL) {
        a->right->parent = b;
    }

    /* Put b's field's in a */
    a->parent = b->parent;
    a->left = b->left;
    a->right = b->right;
    a->bal = b->bal;

    /* Put a in b's spot */
    if (b->parent != NULL && b->parent->left == b) {
        b->parent->left = a;
    } else if (b->parent != NULL) {
        b->parent->right = a;
    }
    if (b->left != NULL) {
        b->left->parent = a;
    }
    if (b->right != NULL) {
        b->right->parent = a;
    }

    /* Put a's fields in b */
    b->parent = tmp.parent;
    b->left = tmp.left;
    b->right = tmp.right;
    b->bal = tmp.bal;
}

/* Deletion function. 
 *
 * rec - Record to remove from its map
 *
 * Returns the root of the updated tree. NOTE: Does not free any memory used
 * by the record. */
SMEDLRecordBase * monitor_map_remove(SMEDLRecordBase *rec) {
    if (rec->equal_prev != NULL) {
        /* Not the only record with this key. Remove it without touching the
         * tree. */
        rec->equal_prev->equal = rec->equal;
        if (rec->equal != NULL) {
            rec->equal->equal_prev =rec->equal_prev;
        }

        /* Return the root of the tree unchanged */
        while (rec->equal_prev != NULL) {
            rec = rec->equal_prev;
        }
        while (rec->parent != NULL) {
            rec = rec->parent;
        }
        return rec;
    } else if (rec->equal != NULL) {
        /* Not the only record with this key, but is the head of this key's
         * linked list. Make the next element the new head while removing this
         * record. */
        rec->equal->parent = rec->parent;
        rec->equal->left = rec->left;
        rec->equal->right = rec->right;
        rec->equal->bal = rec->bal;
        rec->equal->equal_prev = NULL;
        if (rec->parent != NULL && rec->parent->left == rec) {
            rec->parent->left = rec->equal;
        } else if (rec->parent != NULL) {
            rec->parent->right = rec->equal;
        }
        if (rec->left != NULL) {
            rec->left->parent = rec->equal;
        }
        if (rec->right != NULL) {
            rec->right->parent = rec->equal;
        }

        /* Return the root of the tree unchanged */
        rec = rec->equal;
        while (rec->parent != NULL) {
            rec = rec->parent;
        }
        return rec;
    }

    /* Only record left with this key. It must be removed from the tree. Do
     * the standard BST deletion: If no children, simply remove. If one child,
     * remove and put the child in its place. If two children, swap it with 
     * its successor and try again. */
    SMEDLRecordBase *node = NULL;
    int bal_change;
    while (node == NULL) {
        if (rec->left == NULL) {
            if (rec->right == NULL) {
                /* Record has no children. Remove it now. */
                node = rec->parent;
                if (node == NULL) {
                    /* Last record in the tree. Return empty tree. */
                    return NULL;
                } else if (node->left = rec) {
                    node->left = NULL;
                    bal_change = 1;
                } else {
                    node->right = NULL;
                    bal_change = -1;
                }
            } else {
                /* Record has only right child. Replace with child. */
                node = rec->parent;
                if (node == NULL) {
                    /* Record is root. Make child new root. */
                    rec->right->parent = NULL;
                    return rec->right;
                } else if (node->left = rec) {
                    node->left = rec->right;
                    rec->right->parent = node;
                    bal_change = 1;
                } else {
                    node->right = rec->right;
                    rec->right->parent = node;
                    bal_change = -1;
                }
            }
        } else {
            if (rec->right == NULL) {
                /* Record has only left child. Replace with child. */
                node = rec->parent;
                if (node == NULL) {
                    /* Record is root. Make child new root. */
                    rec->left->parent = NULL;
                    return rec->left;
                } else if (node->left = rec) {
                    node->left = rec->left;
                    rec->left->parent = node;
                    bal_change = 1;
                } else {
                    node->right = rec->left;
                    rec->left->parent = node;
                    bal_change = -1;
                }
            } else {
                /* Record has two children. Find the record with the next
                 * highest key and swap with it. Then try again. */
                SMEDLRecordBase *successor;
                for (successor = rec->right; successor->left != NULL;
                        successor = successor->left);
                swap_records(rec, successor);
            }
        }
    }

    /* Rebalance */
    do {
        node->bal += bal_change;

        /* Do rotations or prepare parent's balance correction if
         * necessary */
        switch (node->bal) {
            case 0:
                /* Height of this branch shrunk. Figure out which child we are
                 * and update bal_change. */
                if (node->parent == NULL) {
                    /* At the root. Nothing else to do. */
                    return node;
                } else if (node == node->parent->left) {
                    bal_change = 1;
                } else {
                    bal_change = -1;
                }
                node = node->parent;
                break;
            case -2:
                /* Needs rebalance to the right */
                if (node->left->bal == 0) {
                    /* Left-left case */
                    node->bal = -1;
                    right_rotate(&node);
                    node->bal = 1;
                } else if (node->left->bal < 0) {
                    /* Left-left case */
                    node->bal = 0;
                    right_rotate(&node);
                    node->bal = 0;
                } else {
                    /* Left-right case */
                    left_rotate(&node->left);
                    right_rotate(&node);
                    if (node->bal < 0) {
                        node->left->bal = 0;
                        node->right->bal = 1;
                    } else if (node->bal > 0) {
                        node->left->bal = -1;
                        node->right->bal = 0;
                    } else {
                        node->left->bal = 0;
                        node->right->bal = 0;
                    }
                    node->bal = 0;
                }
                break;
            case 2:
                /* Needs rebalance to the left */
                if (node->right->bal == 0) {
                    /* Right-right case */
                    node->bal = 1;
                    left_rotate(&node);
                    node->bal = -1;
                } else if (node->right->bal > 0) {
                    /* Right-right case */
                    node->bal = 0;
                    left_rotate(&node);
                    node->bal = 0;
                } else {
                    /* Right-left case */
                    right_rotate(&node->right);
                    left_rotate(&node);
                    if (node->bal < 0) {
                        node->left->bal = 0;
                        node->right->bal = 1;
                    } else if (node->bal > 0) {
                        node->left->bal = -1;
                        node->right->bal = 0;
                    } else {
                        node->left->bal = 0;
                        node->right->bal = 0;
                    }
                    node->bal = 0;
                }
                break;
        }
    /* If the current node's balance factor is -1 or 1, the height of its branch
     * did not change (balance factor must have been zero before). Balance
     * correction is complete. */
    } while (node->bal != -1 && node->bal != 1);

    /* Return the new root */
    while (node->parent != NULL) {
        node = node->parent;
    }
    return node;
}

/* Lookup function
 *
 * root - Root of the map to lookup from
 * key - Key to lookup records for
 *
 * Returns a linked list of matching records (linked with ->equal member) */
SMEDLRecordBase * monitor_map_lookup(SMEDLRecordBase *root, SMEDLValue key) {
    while (root != NULL) {
        int cmp = smedl_compare(key, root->key);

        if (cmp < 0) {
            /* Traverse left */
            root = root->left;
        } else if (cmp > 0) {
            /* Traverse right */
            root = root->right;
        } else {
            /* Found it */
            return root;
        }
    }
    
    /* Reached a leaf and didn't find it */
    return NULL;
}

/* Fetch all monitors
 *
 * Return a linked list of all monitors in the map (linked with ->next
 * member) */
SMEDLRecordBase * monitor_map_all(SMEDLRecordBase *root) {
    /* Construct the results list. There are two categories of records:
     * the tree nodes and the non tree nodes (records with the same key as a
     * tree node that are in the tree node's ->equal linked list). 
     * Tree nodes are added to the tail of the list, starting with the root.
     * Non tree nodes are added to the head of the list. Iterate through
     * the list toward the tail to visit every tree node and get their children
     * and equals. */
    SMEDLRecordBase *tail = root; 
    SMEDLRecordBase *head = root;
    for (SMEDLRecordBase *curr = root; curr != NULL; curr = curr->next) {
        /* Add equals to the head */
        for (SMEDLRecordBase *eq = curr->equal; eq != NULL; eq = eq->equal) {
            eq->next = head;
            head = eq;
        }
        /* Add children to the tail */
        if (curr->left != NULL) {
            tail->next = curr->left;
            tail = tail->next;
        }
        if (curr->right != NULL) {
            tail->next = curr->right;
            tail = tail->next;
        }
        tail->next = NULL;
    }

    return head;
}
