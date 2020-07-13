#include "unity.h"
#include "global_event_queue.h"

/* Create a DUMMY pointer that doesn't point to anything meaningful but can be
 * used where an arbirary pointer is required, or DUMMY + x (for x up to 10) for
 * more pointers */
int dummy[10];
void *DUMMY = dummy;

/* Make a SMEDLValue for the provided int */
SMEDLValue smedl_val(int i) {
    return (SMEDLValue) {.t = SMEDL_INT, .v = {.i = i}};
}

void setUp(void) {
}

void tearDown(void) {
}

void test_pop_empty(void) {
    GlobalEventQueue q = {0};
    int chan;
    SMEDLValue *params, *ids;
    void *aux;

    TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params, &aux),
            "Popping from empty queue did not fail");
}

void test_push_pop_one(void) {
    GlobalEventQueue q = {0};
    int chan;
    SMEDLValue *params, *ids;
    void *aux;

    SMEDLValue p[] = {{.t = SMEDL_INT, .v = {.i = 123}}}
    SMEDLValue id[] = {{.t = SMEDL_INT, .v = {.i = 456}}}

    TEST_ASSERT_TRUE_MESSAGE(push_global_event(&q, 2, id, p, DUMMY),
            "Pusing to empty queue failed");
    TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params, &aux),
            "Popping last item from queue failed");
    TEST_ASSERT_INT_EQUAL_MESSAGE(2, chan,
            "Popped channel ID does not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(id, ids,
            "Popped monitor params do not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(p, params,
            "Popped event params do not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(DUMMY, aux,
            "Popped aux pointer does not match pushed");
    TEST_ASSERT_NULL_MESSAGE(q->head,
            "Queue head not NULL after popping only event");
    TEST_ASSERT_NULL_MESSAGE(q->tail,
            "Queue tail not NULL after popping only event");
}

void test_push_pop_no_aux(void) {
    GlobalEventQueue q = {0};
    int chan;
    SMEDLValue *params, *ids;
    void *aux;

    SMEDLValue p[] = {{.t = SMEDL_INT, .v = {.i = 123}}}
    SMEDLValue id[] = {{.t = SMEDL_INT, .v = {.i = 456}}}

    TEST_ASSERT_TRUE_MESSAGE(push_global_event(&q, 2, id, p, NULL),
            "Pusing to empty queue failed");
    TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params, &aux),
            "Popping last item from queue failed");
    TEST_ASSERT_INT_EQUAL_MESSAGE(2, chan,
            "Popped channel ID does not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(id, ids,
            "Popped monitor params do not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(p, params,
            "Popped event params do not match pushed");
    TEST_ASSERT_PTR_EQUAL_MESSAGE(NULL, aux,
            "Popped aux pointer does not match pushed");
    TEST_ASSERT_NULL_MESSAGE(q->head,
            "Queue head not NULL after popping only event");
    TEST_ASSERT_NULL_MESSAGE(q->tail,
            "Queue tail not NULL after popping only event");
}

void test_push_pop_many(void) {
    GlobalEventQueue q = {0};
    int chan;
    SMEDLValue *params, *ids;
    void *aux;

    SMEDLValue p[10][1]; {
        {.t = SMEDL_INT, .v = {.i = 10}},
        {.t = SMEDL_INT, .v = {.i = 20}},
        {.t = SMEDL_INT, .v = {.i = 30}},
        {.t = SMEDL_INT, .v = {.i = 40}},
        {.t = SMEDL_INT, .v = {.i = 50}},
        {.t = SMEDL_INT, .v = {.i = 60}},
        {.t = SMEDL_INT, .v = {.i = 70}},
        {.t = SMEDL_INT, .v = {.i = 80}},
        {.t = SMEDL_INT, .v = {.i = 90}},
        {.t = SMEDL_INT, .v = {.i = 100}},
    }
    SMEDLValue id[10][1]; {
        {.t = SMEDL_INT, .v = {.i = 15}},
        {.t = SMEDL_INT, .v = {.i = 25}},
        {.t = SMEDL_INT, .v = {.i = 35}},
        {.t = SMEDL_INT, .v = {.i = 45}},
        {.t = SMEDL_INT, .v = {.i = 55}},
        {.t = SMEDL_INT, .v = {.i = 65}},
        {.t = SMEDL_INT, .v = {.i = 75}},
        {.t = SMEDL_INT, .v = {.i = 85}},
        {.t = SMEDL_INT, .v = {.i = 95}},
        {.t = SMEDL_INT, .v = {.i = 105}},
    }
    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_TRUE_MESSAGE(push_global_event(&q, i, id[i], p[i],
                DUMMY + i), "Pusing to queue failed");
    }

    for (int i = 0; i < 10; i++) {
        TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params,
                &aux), "Popping item from queue failed");
        TEST_ASSERT_INT_EQUAL_MESSAGE(i, chan,
                "Popped channel ID does not match pushed");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(id[i], ids,
                "Popped monitor params do not match pushed");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(p[i], params,
                "Popped event params do not match pushed");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(DUMMY + i, aux,
                "Popped aux pointer does not match pushed");
    }

    TEST_ASSERT_NULL_MESSAGE(q->head,
            "Queue head not NULL after popping last event");
    TEST_ASSERT_NULL_MESSAGE(q->tail,
            "Queue tail not NULL after popping last event");
}

void test_push_pop_push_pop(void) {
    GlobalEventQueue q = {0};
    int chan;
    SMEDLValue *params, *ids;
    void *aux;

    SMEDLValue p[10][1]; {
        {.t = SMEDL_INT, .v = {.i = 10}},
        {.t = SMEDL_INT, .v = {.i = 20}},
        {.t = SMEDL_INT, .v = {.i = 30}},
        {.t = SMEDL_INT, .v = {.i = 40}},
        {.t = SMEDL_INT, .v = {.i = 50}},
        {.t = SMEDL_INT, .v = {.i = 60}},
        {.t = SMEDL_INT, .v = {.i = 70}},
        {.t = SMEDL_INT, .v = {.i = 80}},
        {.t = SMEDL_INT, .v = {.i = 90}},
        {.t = SMEDL_INT, .v = {.i = 100}},
    }
    SMEDLValue id[10][1]; {
        {.t = SMEDL_INT, .v = {.i = 15}},
        {.t = SMEDL_INT, .v = {.i = 25}},
        {.t = SMEDL_INT, .v = {.i = 35}},
        {.t = SMEDL_INT, .v = {.i = 45}},
        {.t = SMEDL_INT, .v = {.i = 55}},
        {.t = SMEDL_INT, .v = {.i = 65}},
        {.t = SMEDL_INT, .v = {.i = 75}},
        {.t = SMEDL_INT, .v = {.i = 85}},
        {.t = SMEDL_INT, .v = {.i = 95}},
        {.t = SMEDL_INT, .v = {.i = 105}},
    }
    for (int i = 0; i < 7; i++) {
        TEST_ASSERT_TRUE_MESSAGE(push_global_event(&q, i, id[i], p[i],
                DUMMY + i), "Pusing to queue failed (1st group)");
    }

    for (int i = 0; i < 4; i++) {
        TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params,
                &aux), "Popping item from queue failed (1st group)");
        TEST_ASSERT_INT_EQUAL_MESSAGE(i, chan,
                "Popped channel ID does not match pushed (1st group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(id[i], ids,
                "Popped monitor params do not match pushed (1st group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(p[i], params,
                "Popped event params do not match pushed (1st group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(DUMMY + i, aux,
                "Popped aux pointer does not match pushed (1st group)");
    }

    for (int i = 7; i < 10; i++) {
        TEST_ASSERT_TRUE_MESSAGE(push_global_event(&q, i, id[i], p[i],
                DUMMY + i), "Pusing to queue failed (2nd group)");
    }

    for (int i = 4; i < 10; i++) {
        TEST_ASSERT_FALSE_MESSAGE(pop_global_event(&q, &chan, &ids, &params,
                &aux), "Popping item from queue failed (2nd group)");
        TEST_ASSERT_INT_EQUAL_MESSAGE(i, chan,
                "Popped channel ID does not match pushed (2nd group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(id[i], ids,
                "Popped monitor params do not match pushed (2nd group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(p[i], params,
                "Popped event params do not match pushed (2nd group)");
        TEST_ASSERT_PTR_EQUAL_MESSAGE(DUMMY + i, aux,
                "Popped aux pointer does not match pushed (2nd group)");
    }

    TEST_ASSERT_NULL_MESSAGE(q->head,
            "Queue head not NULL after popping last event");
    TEST_ASSERT_NULL_MESSAGE(q->tail,
            "Queue tail not NULL after popping last event");
}

int main(void) {
    UNITY_BEGIN();
    RUN_TEST(test_pop_empty);
    RUN_TEST(test_push_pop_one);
    RUN_TEST(test_push_pop_no_aux);
    RUN_TEST(test_push_pop_many);
    RUN_TEST(test_push_pop_push_pop);
    return UNITY_END();
}
