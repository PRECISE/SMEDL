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
                    if (node->left->bal > 0) {
                        /* Right-right case */
                        node->bal = 0;
                        node = left_rotate(&node);
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

        /* Insert done and tree is balanced. Return the root. */
        while (node->parent != NULL) {
            node = node->parent;
        }
        *root = node;
    }

    /* Found a matching key already present. Add to that key. */
    rec->equal = node->equal;
    node->equal = rec;
    *root = node;
}

/* Lookup function
 *
 * root - Root of the map to lookup from
 * key - Key to lookup records for
 *
 * Returns a linked list of matching records (linked with ->equal member) */
SMEDLRecordBase * monitor_map_lookup(SMEDLRecordBase *root, SMEDLValue *key) {
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
