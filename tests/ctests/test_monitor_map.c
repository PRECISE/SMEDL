#include <stdio.h>
#include "unity.h"
#include "monitor_map.h"

SMEDLRecordBase dummy = {0};
SMEDLRecordBase *DUMMY = &dummy;

/* Mock smedl_compare() - only compares int values, to be used with
 * smedl_val() */
int smedl_compare(SMEDLValue v1, SMEDLValue v2) {
    if (v1.v.i < v2.v.i) {
        return -1;
    } else if (v1.v.i > v2.v.i) {
        return 1;
    } else {
        return 0;
    }
}

/* Make a SMEDLValue for the provided int */
SMEDLValue smedl_val(int i) {
    return (SMEDLValue) {.t = SMEDL_INT, .v = {.i = i}};
}

/* Initialize a SMEDLRecordBase with the given int and dummy values for all
 * pointer members (so if that are not set to NULL, it can be detected) */
void init_record(SMEDLRecordBase *rec, int i) {
    rec->next = DUMMY;
    rec->parent = DUMMY;
    rec->left = DUMMY;
    rec->right = DUMMY;
    rec->equal = DUMMY;
    rec->equal_prev = DUMMY;
    rec->bal = 100;
    rec->key = (SMEDLValue) {.t = SMEDL_INT, .v = {.i = i}};
}

/* Do the following tests on a SMEDLRecordBase.equal memeber:
 * - Every record in the list is equal
 * - First record (the one passed in) has NULL for equal_prev
 * - Every record except the first has NULL for parent, left, and right and
 *   equal_prev is set to the previous record
 * Returns the number of records in the list */
int check_equal_list(SMEDLRecordBase *rec) {
    int count = 0;
    if (rec == NULL) {
        return 0;
    }

    /* Check first (this) record) */
    SMEDLValue v = rec->key;
    count++;
    TEST_ASSERT_NULL_MESSAGE(rec->equal_prev, "First has non-null .equal_prev");

    /* Check the rest */
    while (rec->equal != NULL) {
        SMEDLRecordBase *prev = rec;
        rec = rec->equal;
        count++;

        TEST_ASSERT_EQUAL_MESSAGE(0, smedl_compare(rec->key, v),
                "Key in equal list does not match");
        TEST_ASSERT_EQUAL_PTR_MESSAGE(rec, rec->equal_prev,
                ".equal_prev does not point to prev record");
        TEST_ASSERT_NULL_MESSAGE(rec->parent,
                "Equal record has non-NULL .parent");
        TEST_ASSERT_NULL_MESSAGE(rec->left,
                "Equal record has non-NULL .left");
        TEST_ASSERT_NULL_MESSAGE(rec->right,
                "Equal record has non-NULL .right");
    }

    return count;
}

/* Do the following tests to determine if the AVL tree is valid:
 * - Equal list is correct according to is_equal_list_valid()
 * - Order is correct: left < self < right, for all nodes (i.e. is a BST)
 * - bal is -1, 0, or 1 and properly reflects the balance of the tree,
 *   for all nodes (i.e. is an AVL tree)
 * - Each child's .parent is correct
 * Returns the number of records in the tree. If height is not NULL, the
 * value it points to will be set to the height of the tree. */
int check_avl_tree(SMEDLRecordBase *root, int *height) {
    if (root == NULL) {
        if (height != NULL) {
            *height = 0;
        }
        return 0;
    }

    /* Check equal list */
    int count = check_equal_list(root);

    /* Check left and right children */
    int left_height, right_height;
    count += check_avl_tree(root->left, &left_height);
    count += check_avl_tree(root->right, &right_height);
    
    /* Check balance */
    TEST_ASSERT_INT_WITHIN_MESSAGE(1, 0, right_height - left_height,
            "AVL tree is unbalanced");
    TEST_ASSERT_EQUAL_INT8_MESSAGE(right_height - left_height, root->bal,
            ".bal does not match the balance");
    if (height != NULL) {
        *height = (left_height > right_height) ?
            (left_height + 1) : (right_height + 1);
    }

    /* Check order and parent links */
    if (left_height > 0) {
        TEST_ASSERT_MESSAGE(smedl_compare(root->left->key, root->key) < 0,
                ".left key not less");
        TEST_ASSERT_EQUAL_PTR_MESSAGE(root, root->left->parent,
                ".left.parent is not parent");
    }
    if (right_height > 0) {
        TEST_ASSERT_MESSAGE(smedl_compare(root->right->key, root->key) > 0,
                ".right key not greater");
        TEST_ASSERT_EQUAL_PTR_MESSAGE(root, root->right->parent,
                ".right.parent is not parent");
    }

    return count;
}

/* Return 1 if the record is not in the tree, 0 otherwise */
int check_rec_removed(SMEDLRecordBase *root, SMEDLRecordBase *rec) {
    if (root == NULL) {
        return 1;
    }

    /* Check this node */
    for (SMEDLRecordBase *r = root; r != NULL; r = r->equal) {
        if (r == rec) {
            return 0;
        }
    }

    /* Check children */
    return check_rec_removed(root->left, rec) &&
        check_rec_removed(root->right, rec);
}

/* Return 1 if the record is in the linked list (using SMEDLRecordBase.next),
 * 0 otherwise */
int check_rec_in_list(SMEDLRecordBase *head, SMEDLRecordBase *rec) {
    for (; head != NULL; head = head->next) {
        if (head == rec) {
            return 1;
        }
    }
    return 0;
}

void setUp(void) {
}

void tearDown(void) {
}

void test_empty_control(void) {
    SMEDLRecordBase *map = NULL;
    int height;
    int size = check_avl_tree(map, &height);
    TEST_ASSERT_EQUAL_INT(0, height);
    TEST_ASSERT_EQUAL_INT(0, size);
}

/* Test insertions ***********************************************************/

void test_insert_into_empty(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec;
    init_record(&rec, 10);

    monitor_map_insert(&map, &rec);

    TEST_ASSERT_EQUAL_INT_MESSAGE(1, check_avl_tree(map, NULL),
            "Tree does not have correct size");
}

void test_insert_bigger(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec, rec2;
    init_record(&rec, 10);
    init_record(&rec2, 15);

    monitor_map_insert(&map, &rec);

    TEST_ASSERT_EQUAL_INT_MESSAGE(1, check_avl_tree(map, NULL),
            "Tree does not have correct size before insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(2, check_avl_tree(map, NULL),
            "Tree does not have correct size after insert");
}

void test_insert_smaller(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec, rec2;
    init_record(&rec, 10);
    init_record(&rec2, 5);

    monitor_map_insert(&map, &rec);

    TEST_ASSERT_EQUAL_INT_MESSAGE(1, check_avl_tree(map, NULL),
            "Tree does not have correct size before insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(2, check_avl_tree(map, NULL),
            "Tree does not have correct size after insert");
}

void test_insert_ll(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec1, rec2;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);

    init_record(&rec1, 3);
    init_record(&rec2, 2);
    monitor_map_insert(&map, &rec1);

    int height;
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, check_avl_tree(map, &height),
            "Tree does not have correct size before rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height before rotation insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, &height),
            "Tree does not have correct size after rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height after rotation insert");
}

void test_insert_lr(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec1, rec2;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);

    init_record(&rec1, 3);
    init_record(&rec2, 4);
    monitor_map_insert(&map, &rec1);

    int height;
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, check_avl_tree(map, &height),
            "Tree does not have correct size before rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height before rotation insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, &height),
            "Tree does not have correct size after rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height after rotation insert");
}

void test_insert_rl(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec1, rec2;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);

    init_record(&rec1, 7);
    init_record(&rec2, 6);
    monitor_map_insert(&map, &rec1);

    int height;
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, check_avl_tree(map, &height),
            "Tree does not have correct size before rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height before rotation insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, &height),
            "Tree does not have correct size after rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height after rotation insert");
}

void test_insert_rr(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec1, rec2;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);

    init_record(&rec1, 7);
    init_record(&rec2, 8);
    monitor_map_insert(&map, &rec1);

    int height;
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, check_avl_tree(map, &height),
            "Tree does not have correct size before rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height before rotation insert");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, &height),
            "Tree does not have correct size after rotation insert");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, height,
            "Tree does not have correct height after rotation insert");
}

void test_insert_ascending(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec[20];
    for (int i = 0; i < 20; i++) {
        init_record(&rec[i], i);
    }

    TEST_ASSERT_EQUAL_INT_MESSAGE(0, check_avl_tree(map, NULL),
            "Tree does not have correct size before first insert");

    for (int i = 0; i < 20; i++) {
        char msg[100];
        snprintf(msg, 100, "Tree does not have correct size after insert %d",
                i + 1);
        monitor_map_insert(&map, &rec[i]);
        TEST_ASSERT_EQUAL_INT_MESSAGE(i + 1, check_avl_tree(map, NULL), msg);
    }
}

void test_insert_descending(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec[20];
    for (int i = 0; i < 20; i++) {
        init_record(&rec[i], 9 - i);
    }

    TEST_ASSERT_EQUAL_INT_MESSAGE(0, check_avl_tree(map, NULL),
            "Tree does not have correct size before first insert");

    for (int i = 0; i < 20; i++) {
        char msg[100];
        snprintf(msg, 100, "Tree does not have correct size after insert %d",
                i + 1);
        monitor_map_insert(&map, &rec[i]);
        TEST_ASSERT_EQUAL_INT_MESSAGE(i + 1, check_avl_tree(map, NULL), msg);
    }
}

void test_insert_equals_root(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec1;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);

    init_record(&rec1, 10);

    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size before duplicate insert");
    monitor_map_insert(&map, &rec1);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after duplicate insert");
}

void test_insert_equals_leaf(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec1;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);

    init_record(&rec1, 3);

    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size before duplicate insert");
    monitor_map_insert(&map, &rec1);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after duplicate insert");
}

void test_insert_multiple_equal(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec1, rec2, rec3;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);

    init_record(&rec1, 5);
    init_record(&rec2, 5);
    init_record(&rec3, 5);

    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size before duplicate inserts");
    monitor_map_insert(&map, &rec1);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after duplicate insert 1");
    monitor_map_insert(&map, &rec2);
    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size after duplicate insert 2");
    monitor_map_insert(&map, &rec3);
    TEST_ASSERT_EQUAL_INT_MESSAGE(8, check_avl_tree(map, NULL),
            "Tree does not have correct size after duplicate insert 3");
}

/* Test deletions ************************************************************/

void test_delete_only(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec;
    init_record(&rec, 10);

    monitor_map_insert(&map, &rec);

    TEST_ASSERT_EQUAL_INT_MESSAGE(1, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec);
    TEST_ASSERT_EQUAL_INT_MESSAGE(0, check_avl_tree(map, NULL),
            "Tree is not empty after delete");
}

void test_delete_leaf_l(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 13);
    init_record(&rec_g, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_d);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_leaf_r(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 13);
    init_record(&rec_g, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_e);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_middle_one_child_l(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 13);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);

    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_c);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_middle_one_child_r(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);

    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_c);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_middle(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 13);
    init_record(&rec_g, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_c);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 13);
    init_record(&rec_g, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_leaf_ll(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 2);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_e);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_leaf_lr(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 4);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_e);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_leaf_rl(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 6);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_d);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_leaf_rr(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 8);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_d);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_successor_not_leaf(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);

    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_predecessor_not_leaf(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 13);
    init_record(&rec_f, 17);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);

    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(5, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_left_heavy_l(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 2);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_left_heavy_r(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 17);
    init_record(&rec_g, 4);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_right_heavy_l(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 13);
    init_record(&rec_f, 17);
    init_record(&rec_g, 16);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_root_right_heavy_r(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 13);
    init_record(&rec_f, 17);
    init_record(&rec_g, 18);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
}

void test_delete_ascending(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec[20];
    for (int i = 0; i < 20; i++) {
        init_record(&rec[i], i);
        monitor_map_insert(&map, &rec[i]);
    }

    TEST_ASSERT_EQUAL_INT_MESSAGE(20, check_avl_tree(map, NULL),
            "Tree does not have correct size before first delete");

    for (int i = 0; i < 20; i++) {
        char msg[100];
        snprintf(msg, 100, "Tree does not have correct size after delete %d",
                i + 1);
        monitor_map_remove(&rec[i]);
        TEST_ASSERT_EQUAL_INT_MESSAGE(19 - i, check_avl_tree(map, NULL), msg);
    }
}

void test_delete_descending(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec[20];
    for (int i = 0; i < 20; i++) {
        init_record(&rec[i], i);
        monitor_map_insert(&map, &rec[i]);
    }

    TEST_ASSERT_EQUAL_INT_MESSAGE(20, check_avl_tree(map, NULL),
            "Tree does not have correct size before first delete");

    for (int i = 0; i < 20; i++) {
        char msg[100];
        snprintf(msg, 100, "Tree does not have correct size after delete %d",
                i + 1);
        monitor_map_remove(&rec[19 - i]);
        TEST_ASSERT_EQUAL_INT_MESSAGE(19 - i, check_avl_tree(map, NULL), msg);
    }
}

void test_delete_first_equal_root(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 10);
    init_record(&rec_g, 10);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_a);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
    TEST_ASSERT_MESSAGE(check_rec_removed(map, &rec_a),
            "Record still in map after delete");
}

void test_delete_first_equal_middle(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_b);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
    TEST_ASSERT_MESSAGE(check_rec_removed(map, &rec_b),
            "Record still in map after delete");
}

void test_delete_first_equal_leaf(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 3);
    init_record(&rec_g, 3);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_c);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
    TEST_ASSERT_MESSAGE(check_rec_removed(map, &rec_c),
            "Record still in map after delete");
}

void test_delete_middle_equal(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_f);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
    TEST_ASSERT_MESSAGE(check_rec_removed(map, &rec_f),
            "Record still in map after delete");
}

void test_delete_last_equal(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    TEST_ASSERT_EQUAL_INT_MESSAGE(7, check_avl_tree(map, NULL),
            "Tree does not have correct size before delete");
    monitor_map_remove(&rec_g);
    TEST_ASSERT_EQUAL_INT_MESSAGE(6, check_avl_tree(map, NULL),
            "Tree does not have correct size after delete");
    TEST_ASSERT_MESSAGE(check_rec_removed(map, &rec_g),
            "Record still in map after delete");
}

/* Test lookups **************************************************************/

void test_lookup_empty(void) {
    TEST_ASSERT_NULL_MESSAGE(monitor_map_lookup(NULL, smedl_val(1)),
            "Lookup on empty gave result");
}

void test_lookup_only(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a;
    init_record(&rec_a, 10);
    monitor_map_insert(&map, &rec_a);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(10));
    TEST_ASSERT_EQUAL_PTR_MESSAGE(&rec_a, rec,
            "Did not receive inserted record from lookup");
}

void test_lookup_one_nomatch_left(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a;
    init_record(&rec_a, 10);
    monitor_map_insert(&map, &rec_a);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(9));
    TEST_ASSERT_NULL_MESSAGE(rec, "Lookup on missing record gave result");
}

void test_lookup_one_nomatch_right(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a;
    init_record(&rec_a, 10);
    monitor_map_insert(&map, &rec_a);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(11));
    TEST_ASSERT_NULL_MESSAGE(rec, "Lookup on missing record gave result");
}

void test_lookup_many_nomatch_left(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(1));
    TEST_ASSERT_NULL_MESSAGE(rec, "Lookup on missing record gave result");
}

void test_lookup_many_nomatch_right(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(16));
    TEST_ASSERT_NULL_MESSAGE(rec, "Lookup on missing record gave result");
}

void test_lookup_root(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(10));
    TEST_ASSERT_EQUAL_PTR_MESSAGE(&rec_a, rec,
            "Received wrong record from lookup");
}

void test_lookup_middle(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(5));
    TEST_ASSERT_EQUAL_PTR_MESSAGE(&rec_b, rec,
            "Received wrong record from lookup");
}

void test_lookup_leaf(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec_a, rec_b, rec_c, rec_d, rec_e, rec_f, rec_g;

    init_record(&rec_a, 10);
    init_record(&rec_b, 5);
    init_record(&rec_c, 15);
    init_record(&rec_d, 3);
    init_record(&rec_e, 7);
    init_record(&rec_f, 5);
    init_record(&rec_g, 5);
    monitor_map_insert(&map, &rec_a);
    monitor_map_insert(&map, &rec_b);
    monitor_map_insert(&map, &rec_c);
    monitor_map_insert(&map, &rec_d);
    monitor_map_insert(&map, &rec_e);
    monitor_map_insert(&map, &rec_f);
    monitor_map_insert(&map, &rec_g);

    SMEDLRecordBase *rec;
    rec = monitor_map_lookup(map, smedl_val(7));
    TEST_ASSERT_EQUAL_PTR_MESSAGE(&rec_e, rec,
            "Received wrong record from lookup");
}

/* Test lookup-alls **********************************************************/

void test_lookup_all_empty(void) {
    TEST_ASSERT_NULL_MESSAGE(monitor_map_all(NULL),
            "Lookup all on empty gave result");
}

void test_lookup_all_one(void) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase rec;
    init_record(&rec, 10);
    monitor_map_insert(&map, &rec);

    SMEDLRecordBase *head;
    head = monitor_map_all(map);
    TEST_ASSERT_EQUAL_PTR_MESSAGE(&rec, head,
            "Did not receive inserted record from lookup all");
    TEST_ASSERT_NULL_MESSAGE(head->next,
            "Lookup all result not NULL-terminated");
}

/* Do a test on lookup_all where there are n records with values specified by
 * vals, inserted in that order. Assert that each record is in the resulting
 * map. */
void do_test_lookup_all(int n, int vals[n]) {
    SMEDLRecordBase *map = NULL;

    SMEDLRecordBase recs[n];
    for (int i = 0; i < n; i++) {
        init_record(&recs[i], vals[i]);
        monitor_map_insert(&map, &recs[i]);
    }

    SMEDLRecordBase *head = monitor_map_all(map);
    for (int i = 0; i < n; i++) {
        TEST_ASSERT_MESSAGE(check_rec_in_list(head, &recs[i]),
                "Record missing from lookup all");
    }
}

void test_lookup_all_many(void) {
    int vals[] = {10, 5, 15, 3, 7, 13, 17};
    do_test_lookup_all(sizeof(vals) / sizeof(vals[0]), vals);
}

void test_lookup_all_equal_in_root(void) {
    int vals[] = {10, 5, 15, 3, 7, 10, 10};
    do_test_lookup_all(sizeof(vals) / sizeof(vals[0]), vals);
}

void test_lookup_all_equal_in_middle(void) {
    int vals[] = {10, 5, 15, 3, 7, 5, 5};
    do_test_lookup_all(sizeof(vals) / sizeof(vals[0]), vals);
}

void test_lookup_all_equal_in_leaf(void) {
    int vals[] = {10, 5, 15, 3, 7, 3, 3};
    do_test_lookup_all(sizeof(vals) / sizeof(vals[0]), vals);
}

void test_lookup_all_many_equal(void) {
    int vals[] = {10, 5, 15, 3, 3, 3, 13, 13, 17, 10, 10, 10, 5};
    do_test_lookup_all(sizeof(vals) / sizeof(vals[0]), vals);
}

/*****************************************************************************/

int main(void) {
    UNITY_BEGIN();
    RUN_TEST(test_empty_control);

    RUN_TEST(test_insert_into_empty);
    RUN_TEST(test_insert_bigger);
    RUN_TEST(test_insert_smaller);
    RUN_TEST(test_insert_ll);
    RUN_TEST(test_insert_lr);
    RUN_TEST(test_insert_rl);
    RUN_TEST(test_insert_rr);
    RUN_TEST(test_insert_ascending);
    RUN_TEST(test_insert_descending);
    RUN_TEST(test_insert_equals_root);
    RUN_TEST(test_insert_equals_leaf);
    RUN_TEST(test_insert_multiple_equal);

    RUN_TEST(test_delete_only);
    RUN_TEST(test_delete_leaf_l);
    RUN_TEST(test_delete_leaf_r);
    RUN_TEST(test_delete_middle_one_child_l);
    RUN_TEST(test_delete_middle_one_child_r);
    RUN_TEST(test_delete_middle);
    RUN_TEST(test_delete_root);
    RUN_TEST(test_delete_leaf_ll);
    RUN_TEST(test_delete_leaf_lr);
    RUN_TEST(test_delete_leaf_rl);
    RUN_TEST(test_delete_leaf_rr);
    RUN_TEST(test_delete_root_successor_not_leaf);
    RUN_TEST(test_delete_root_predecessor_not_leaf);
    RUN_TEST(test_delete_root_left_heavy_l);
    RUN_TEST(test_delete_root_left_heavy_r);
    RUN_TEST(test_delete_root_right_heavy_l);
    RUN_TEST(test_delete_root_right_heavy_r);
    RUN_TEST(test_delete_ascending);
    RUN_TEST(test_delete_descending);
    RUN_TEST(test_delete_first_equal_root);
    RUN_TEST(test_delete_first_equal_middle);
    RUN_TEST(test_delete_first_equal_leaf);
    RUN_TEST(test_delete_middle_equal);
    RUN_TEST(test_delete_last_equal);

    RUN_TEST(test_lookup_empty);
    RUN_TEST(test_lookup_only);
    RUN_TEST(test_lookup_one_nomatch_left);
    RUN_TEST(test_lookup_one_nomatch_right);
    RUN_TEST(test_lookup_many_nomatch_left);
    RUN_TEST(test_lookup_many_nomatch_right);
    RUN_TEST(test_lookup_root);
    RUN_TEST(test_lookup_middle);
    RUN_TEST(test_lookup_leaf);

    RUN_TEST(test_lookup_all_empty);
    RUN_TEST(test_lookup_all_one);
    RUN_TEST(test_lookup_all_many);
    RUN_TEST(test_lookup_all_equal_in_root);
    RUN_TEST(test_lookup_all_equal_in_middle);
    RUN_TEST(test_lookup_all_equal_in_leaf);
    RUN_TEST(test_lookup_all_many_equal);

    RUN_TEST(test_lookup_empty);
    return UNITY_END();
}
