#include <stdlib.h>
#include <string.h>
#include "unity.h"
#include "smedl_types.h"

/* Return a SMEDLOpaque formed from the given string */
SMEDLOpaque make_opaque(char *str) {
    SMEDLOpaque o;
    o.data = str;
    o.size = strlen(str);
    return o;
}

void setUp(void) {
}

void tearDown(void) {
}

void test_opaque_equals_empty(void) {
    SMEDLOpaque o1 = make_opaque("");
    SMEDLOpaque o2 = make_opaque("");
    TEST_ASSERT_TRUE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Empty opaques not equal");
}

void test_opaque_equals_first_empty(void) {
    SMEDLOpaque o1 = make_opaque("");
    SMEDLOpaque o2 = make_opaque("fgh");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Empty first equal to nonempty second");
}

void test_opaque_equals_second_empty(void) {
    SMEDLOpaque o1 = make_opaque("fgh");
    SMEDLOpaque o2 = make_opaque("");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Nonempty first equal to empty second");
}

void test_opaque_equals_equal(void) {
    SMEDLOpaque o1 = make_opaque("fgh");
    SMEDLOpaque o2 = make_opaque("fgh");
    TEST_ASSERT_TRUE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Nonempty opaques not equal");
}

void test_opaque_equals_first_shorter(void) {
    SMEDLOpaque o1 = make_opaque("fg");
    SMEDLOpaque o2 = make_opaque("fgh");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Shorter opaque equal to longer");
}

void test_opaque_equals_second_shorter(void) {
    SMEDLOpaque o1 = make_opaque("fgh");
    SMEDLOpaque o2 = make_opaque("fg");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Longer opaque equal to shorter");
}

void test_opaque_equals_unequal_same_length(void) {
    SMEDLOpaque o1 = make_opaque("fgh");
    SMEDLOpaque o2 = make_opaque("abc");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Different opaques with same length equal");
}

void test_opaque_equals_unequal_different_length(void) {
    SMEDLOpaque o1 = make_opaque("fgh");
    SMEDLOpaque o2 = make_opaque("ab");
    TEST_ASSERT_FALSE_MESSAGE(smedl_opaque_equals(o1, o2),
            "Different opaques euqal");
}

void test_assign_string_empty(void) {
    char *src = "";
    char *dst;
    TEST_ASSERT_TRUE_MESSAGE(smedl_assign_string(&dst, src),
            "smedl_assign_string() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src, dst,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_STRING_MESSAGE(src, dst,
            "dst and src do not match");
    free(dst);
}

void test_assign_string_nonempty(void) {
    char *src = "abc";
    char *dst;
    TEST_ASSERT_TRUE_MESSAGE(smedl_assign_string(&dst, src),
            "smedl_assign_string() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src, dst,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_STRING_MESSAGE(src, dst,
            "dst and src do not match");
    free(dst);
}

void test_assign_opaque_empty(void) {
    SMEDLOpaque src = make_opaque("");
    SMEDLOpaque dst;
    TEST_ASSERT_TRUE_MESSAGE(smedl_assign_opaque(&dst, src),
            "smedl_assign_opaque() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src.data, dst.data,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_MESSAGE(src.size, dst.size,
            "dst not same size as src");
    /* Unity fails TEST_ASSERT_EQUAL_MEMORY when length is zero */
    /*TEST_ASSERT_EQUAL_MEMORY_MESSAGE(src.data, dst.data, src.size,
            "dst and src do not match");*/
    free(dst.data);
}

void test_assign_opaque_nonempty(void) {
    SMEDLOpaque src = make_opaque("abc");
    SMEDLOpaque dst;
    TEST_ASSERT_TRUE_MESSAGE(smedl_assign_opaque(&dst, src),
            "smedl_assign_opaque() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src.data, dst.data,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_MESSAGE(src.size, dst.size,
            "dst not same size as src");
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE(src.data, dst.data, src.size,
            "dst and src do not match");
    free(dst.data);
}

void test_replace_string_empty(void) {
    char *src = "";
    char *dst = malloc(1);
    TEST_ASSERT_TRUE_MESSAGE(smedl_replace_string(&dst, src),
            "smedl_replace_string() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src, dst,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_STRING_MESSAGE(src, dst,
            "dst and orig do not match");
    free(dst);
}

void test_replace_string_nonempty(void) {
    char *src = "abc";
    char *dst = malloc(1);
    TEST_ASSERT_TRUE_MESSAGE(smedl_replace_string(&dst, src),
            "smedl_replace_string() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src, dst,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_STRING_MESSAGE(src, dst,
            "dst and orig do not match");
    free(dst);
}

void test_replace_opaque_empty(void) {
    SMEDLOpaque src = make_opaque("");
    SMEDLOpaque dst;
    dst.data = malloc(1);
    TEST_ASSERT_TRUE_MESSAGE(smedl_replace_opaque(&dst, src),
            "smedl_replace_opaque() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src.data, dst.data,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_MESSAGE(src.size, dst.size,
            "dst not same size as orig");
    /* Unity fails TEST_ASSERT_EQUAL_MEMORY when length is zero */
    /* TEST_ASSERT_EQUAL_MEMORY_MESSAGE(src.data, dst.data, src.size,
            "dst and orig do not match"); */
    free(dst.data);
}

void test_replace_opaque_nonempty(void) {
    SMEDLOpaque src = make_opaque("abc");
    SMEDLOpaque dst;
    dst.data = malloc(1);
    TEST_ASSERT_TRUE_MESSAGE(smedl_replace_opaque(&dst, src),
            "smedl_replace_opaque() failed");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src.data, dst.data,
            "dst not a separate copy from src");
    TEST_ASSERT_EQUAL_MESSAGE(src.size, dst.size,
            "dst not same size as orig");
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE(src.data, dst.data, src.size,
            "dst and orig do not match");
    free(dst.data);
}

void test_smedl_compare_int_less(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 1}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser int did not compare less than greater");
}

void test_smedl_compare_int_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 2}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal ints did not compare equal");
}

void test_smedl_compare_int_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 3}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater int did not compare greater than lesser");
}

void test_smedl_compare_float_less(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 1.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser float did not compare less than greater");
}

void test_smedl_compare_float_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal floats did not compare equal");
}

void test_smedl_compare_float_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 3.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater float did not compare greater than lesser");
}

void test_smedl_compare_char_less(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 1}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser char did not compare less than greater");
}

void test_smedl_compare_char_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal chars did not compare equal");
}

void test_smedl_compare_char_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 3}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater char did not compare greater than lesser");
}

void test_smedl_compare_pointer_less(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[1]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser pointer did not compare less than greater");
}

void test_smedl_compare_pointer_equal(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal pointers did not compare equal");
}

void test_smedl_compare_pointer_greater(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[3]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater pointer did not compare greater than lesser");
}

void test_smedl_compare_string_empty(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = ""}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = ""}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Empty strings did not compare equal");
}

void test_smedl_compare_string_first_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fg"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Shorter string did not compare lesser");
}

void test_smedl_compare_string_second_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fg"}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Longer string did not compare greater");
}

void test_smedl_compare_string_first_less(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "abc"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser string did not compare lesser");
}

void test_smedl_compare_string_second_less(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "abc"}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater string did not compare greater");
}

void test_smedl_compare_string_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal strings did not compare equal");
}

void test_smedl_compare_opaque_empty(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Empty strings did not compare equal");
}

void test_smedl_compare_opaque_first_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fg");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Shorter string did not compare lesser");
}

void test_smedl_compare_opaque_second_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fg");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Longer string did not compare greater");
}

void test_smedl_compare_opaque_first_less(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("abc");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) < 0,
            "Lesser string did not compare lesser");
}

void test_smedl_compare_opaque_second_less(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("abc");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) > 0,
            "Greater string did not compare greater");
}

void test_smedl_compare_opaque_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_MESSAGE(smedl_compare(v1, v2) == 0,
            "Equal strings did not compare equal");
}

void test_smedl_equal_int_less(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 1}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser int did not compare unequal to greater");
}

void test_smedl_equal_int_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 2}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal ints did not compare equal");
}

void test_smedl_equal_int_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_INT, .v = {.i = 3}};
    SMEDLValue v2 = {.t = SMEDL_INT, .v = {.i = 2}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater int did not compare unequal to lesser");
}

void test_smedl_equal_float_less(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 1.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser float did not compare unequal to greater");
}

void test_smedl_equal_float_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal floats did not compare equal");
}

void test_smedl_equal_float_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_FLOAT, .v = {.d = 3.0}};
    SMEDLValue v2 = {.t = SMEDL_FLOAT, .v = {.d = 2.0}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater float did not compare unequal to lesser");
}

void test_smedl_equal_char_less(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 1}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser char did not compare unequal to greater");
}

void test_smedl_equal_char_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal chars did not compare equal");
}

void test_smedl_equal_char_greater(void) {
    SMEDLValue v1 = {.t = SMEDL_CHAR, .v = {.c = 3}};
    SMEDLValue v2 = {.t = SMEDL_CHAR, .v = {.c = 2}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater char did not compare unequal to lesser");
}

void test_smedl_equal_pointer_less(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[1]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser pointer did not compare unequal to greater");
}

void test_smedl_equal_pointer_equal(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal pointers did not compare equal");
}

void test_smedl_equal_pointer_greater(void) {
    int tgt[4];
    SMEDLValue v1 = {.t = SMEDL_POINTER, .v = {.p = &tgt[3]}};
    SMEDLValue v2 = {.t = SMEDL_POINTER, .v = {.p = &tgt[2]}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater pointer did not compare unequal to lesser");
}

void test_smedl_equal_string_empty(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = ""}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = ""}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Empty strings did not compare equal");
}

void test_smedl_equal_string_first_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fg"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Shorter string did not compare unequal");
}

void test_smedl_equal_string_second_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fg"}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Longer string did not compare unequal");
}

void test_smedl_equal_string_first_less(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "abc"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser string did not compare unequal");
}

void test_smedl_equal_string_second_less(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "abc"}};
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater string did not compare unequal");
}

void test_smedl_equal_string_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    SMEDLValue v2 = {.t = SMEDL_STRING, .v = {.s = "fgh"}};
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal strings did not compare equal");
}

void test_smedl_equal_opaque_empty(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("");
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Empty opaques did not compare equal");
}

void test_smedl_equal_opaque_first_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fg");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Shorter string did not compare unequal");
}

void test_smedl_equal_opaque_second_shorter(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fg");
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Longer string did not compare unequal");
}

void test_smedl_equal_opaque_first_less(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("abc");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Lesser string did not compare unequal");
}

void test_smedl_equal_opaque_second_less(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("abc");
    TEST_ASSERT_FALSE_MESSAGE(smedl_equal(v1, v2),
            "Greater string did not compare unequal");
}

void test_smedl_equal_opaque_equal(void) {
    SMEDLValue v1 = {.t = SMEDL_OPAQUE};
    v1.v.o = make_opaque("fgh");
    SMEDLValue v2 = {.t = SMEDL_OPAQUE};
    v2.v.o = make_opaque("fgh");
    TEST_ASSERT_TRUE_MESSAGE(smedl_equal(v1, v2),
            "Equal strings did not compare equal");
}

void test_smedl_copy_array_empty(void) {
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    SMEDLValue *dst = smedl_copy_array(NULL, 0);
    free(dst);
}

void test_smedl_copy_array_nonempty(void) {
    SMEDLValue src[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    SMEDLValue *dst = smedl_copy_array(src, 3);
    TEST_ASSERT_NOT_NULL_MESSAGE(dst,
            "Could not copy array of ints");
    TEST_ASSERT_MESSAGE(dst[0].t == SMEDL_INT,
            "First array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(2, dst[0].v.i,
            "First array element value is wrong");
    TEST_ASSERT_MESSAGE(dst[1].t == SMEDL_INT,
            "Second array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, dst[1].v.i,
            "Second array element value is wrong");
    TEST_ASSERT_MESSAGE(dst[2].t == SMEDL_INT,
            "Third array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, dst[2].v.i,
            "Third array element value is wrong");
    free(dst);
}

void test_smedl_copy_array_with_string(void) {
    SMEDLValue src[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_STRING, .v = {.s = "abc"}},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    SMEDLValue *dst = smedl_copy_array(src, 3);
    TEST_ASSERT_NOT_NULL_MESSAGE(dst,
            "Could not copy array of ints");
    TEST_ASSERT_MESSAGE(dst[0].t == SMEDL_INT,
            "First array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(2, dst[0].v.i,
            "First array element value is wrong");
    TEST_ASSERT_MESSAGE(dst[1].t == SMEDL_STRING,
            "Second array element type is wrong");
    TEST_ASSERT_EQUAL_STRING_MESSAGE("abc", dst[1].v.s,
            "Second array element value is wrong");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src[1].v.s, src[2].v.s,
            "String element is not a distinct copy");
    TEST_ASSERT_MESSAGE(dst[2].t == SMEDL_INT,
            "Third array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(4, dst[2].v.i,
            "Third array element value is wrong");
    free(dst[1].v.s);
    free(dst);
}

void test_smedl_copy_array_with_opaque(void) {
    SMEDLValue src[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_OPAQUE},
    };
    src[2].v.o = make_opaque("fgh");
    SMEDLValue *dst = smedl_copy_array(src, 3);
    TEST_ASSERT_NOT_NULL_MESSAGE(dst,
            "Could not copy array of ints");
    TEST_ASSERT_MESSAGE(dst[0].t == SMEDL_INT,
            "First array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(2, dst[0].v.i,
            "First array element value is wrong");
    TEST_ASSERT_MESSAGE(dst[1].t == SMEDL_INT,
            "Second array element type is wrong");
    TEST_ASSERT_EQUAL_INT_MESSAGE(3, dst[1].v.i,
            "Second array element value is wrong");
    TEST_ASSERT_MESSAGE(dst[2].t == SMEDL_OPAQUE,
            "Third array element type is wrong");
    TEST_ASSERT_EQUAL_MESSAGE(strlen("fgh"), dst[2].v.o.size,
            "Opaque element size is wrong");
    TEST_ASSERT_EQUAL_MEMORY_MESSAGE("fgh", dst[2].v.o.data, dst[2].v.o.size,
            "Third array element value is wrong");
    TEST_ASSERT_NOT_EQUAL_MESSAGE(src[1].v.o.data, src[2].v.o.data,
            "String element is not a distinct copy");
    free(dst[2].v.o.data);
    free(dst);
}

void test_smedl_free_array_empty(void) {
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array(NULL, 0);
}

void test_smedl_free_array_nonempty(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array(copy, 3);
}

void test_smedl_free_array_with_string(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_STRING},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    char *str = "fgh";
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    copy[1].v.s = malloc(strlen(str) + 1);
    memcpy(copy[1].v.s, str, strlen(str) + 1);
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array(copy, 3);
}

void test_smedl_free_array_with_opaque(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_OPAQUE},
    };
    char *str = "fgh";
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    copy[2].v.o.data = malloc(strlen(str));
    memcpy(copy[2].v.o.data, str, strlen(str));
    copy[2].v.o.size = strlen(str);
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array(copy, 3);
}

void test_smedl_free_array_contents_empty(void) {
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array_contents(NULL, 0);
}

void test_smedl_free_array_contents_nonempty(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array_contents(copy, 3);
    free(copy);
}

void test_smedl_free_array_contents_with_string(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_STRING},
        {.t = SMEDL_INT, .v = {.i = 4}},
    };
    char *str = "fgh";
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    copy[1].v.s = malloc(strlen(str) + 1);
    memcpy(copy[1].v.s, str, strlen(str) + 1);
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array_contents(copy, 3);
    free(copy);
}

void test_smedl_free_array_contents_with_opaque(void) {
    SMEDLValue orig[] = {
        {.t = SMEDL_INT, .v = {.i = 2}},
        {.t = SMEDL_INT, .v = {.i = 3}},
        {.t = SMEDL_OPAQUE},
    };
    char *str = "fgh";
    SMEDLValue *copy = malloc(sizeof(orig));
    memcpy(copy, orig, sizeof(orig));
    copy[2].v.o.data = malloc(strlen(str));
    memcpy(copy[2].v.o.data, str, strlen(str));
    copy[2].v.o.size = strlen(str);
    
    /* Nothing that can be validated, so just make sure it doesn't segfault */
    smedl_free_array_contents(copy, 3);
    free(copy);
}

int main(void) {
    UNITY_BEGIN();
    RUN_TEST(test_opaque_equals_empty);
    RUN_TEST(test_opaque_equals_first_empty);
    RUN_TEST(test_opaque_equals_second_empty);
    RUN_TEST(test_opaque_equals_equal);
    RUN_TEST(test_opaque_equals_first_shorter);
    RUN_TEST(test_opaque_equals_second_shorter);
    RUN_TEST(test_opaque_equals_unequal_same_length);
    RUN_TEST(test_opaque_equals_unequal_different_length);
    RUN_TEST(test_assign_string_empty);
    RUN_TEST(test_assign_string_nonempty);
    RUN_TEST(test_assign_opaque_empty);
    RUN_TEST(test_assign_opaque_nonempty);
    RUN_TEST(test_replace_string_empty);
    RUN_TEST(test_replace_string_nonempty);
    RUN_TEST(test_replace_opaque_empty);
    RUN_TEST(test_replace_opaque_nonempty);
    RUN_TEST(test_smedl_compare_int_less);
    RUN_TEST(test_smedl_compare_int_equal);
    RUN_TEST(test_smedl_compare_int_greater);
    RUN_TEST(test_smedl_compare_float_less);
    RUN_TEST(test_smedl_compare_float_equal);
    RUN_TEST(test_smedl_compare_float_greater);
    RUN_TEST(test_smedl_compare_char_less);
    RUN_TEST(test_smedl_compare_char_equal);
    RUN_TEST(test_smedl_compare_char_greater);
    RUN_TEST(test_smedl_compare_pointer_less);
    RUN_TEST(test_smedl_compare_pointer_equal);
    RUN_TEST(test_smedl_compare_pointer_greater);
    RUN_TEST(test_smedl_compare_string_empty);
    RUN_TEST(test_smedl_compare_string_first_shorter);
    RUN_TEST(test_smedl_compare_string_second_shorter);
    RUN_TEST(test_smedl_compare_string_first_less);
    RUN_TEST(test_smedl_compare_string_second_less);
    RUN_TEST(test_smedl_compare_string_equal);
    RUN_TEST(test_smedl_compare_opaque_empty);
    RUN_TEST(test_smedl_compare_opaque_first_shorter);
    RUN_TEST(test_smedl_compare_opaque_second_shorter);
    RUN_TEST(test_smedl_compare_opaque_first_less);
    RUN_TEST(test_smedl_compare_opaque_second_less);
    RUN_TEST(test_smedl_compare_opaque_equal);
    RUN_TEST(test_smedl_equal_int_less);
    RUN_TEST(test_smedl_equal_int_equal);
    RUN_TEST(test_smedl_equal_int_greater);
    RUN_TEST(test_smedl_equal_float_less);
    RUN_TEST(test_smedl_equal_float_equal);
    RUN_TEST(test_smedl_equal_float_greater);
    RUN_TEST(test_smedl_equal_char_less);
    RUN_TEST(test_smedl_equal_char_equal);
    RUN_TEST(test_smedl_equal_char_greater);
    RUN_TEST(test_smedl_equal_pointer_less);
    RUN_TEST(test_smedl_equal_pointer_equal);
    RUN_TEST(test_smedl_equal_pointer_greater);
    RUN_TEST(test_smedl_equal_string_empty);
    RUN_TEST(test_smedl_equal_string_first_shorter);
    RUN_TEST(test_smedl_equal_string_second_shorter);
    RUN_TEST(test_smedl_equal_string_first_less);
    RUN_TEST(test_smedl_equal_string_second_less);
    RUN_TEST(test_smedl_equal_string_equal);
    RUN_TEST(test_smedl_equal_opaque_empty);
    RUN_TEST(test_smedl_equal_opaque_first_shorter);
    RUN_TEST(test_smedl_equal_opaque_second_shorter);
    RUN_TEST(test_smedl_equal_opaque_first_less);
    RUN_TEST(test_smedl_equal_opaque_second_less);
    RUN_TEST(test_smedl_equal_opaque_equal);
    RUN_TEST(test_smedl_copy_array_empty);
    RUN_TEST(test_smedl_copy_array_nonempty);
    RUN_TEST(test_smedl_copy_array_with_string);
    RUN_TEST(test_smedl_copy_array_with_opaque);
    RUN_TEST(test_smedl_free_array_empty);
    RUN_TEST(test_smedl_free_array_nonempty);
    RUN_TEST(test_smedl_free_array_with_string);
    RUN_TEST(test_smedl_free_array_with_opaque);
    RUN_TEST(test_smedl_free_array_contents_empty);
    RUN_TEST(test_smedl_free_array_contents_nonempty);
    RUN_TEST(test_smedl_free_array_contents_with_string);
    RUN_TEST(test_smedl_free_array_contents_with_opaque);
    return UNITY_END();
}
