#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct heapNode {
    int value;
    int priority;
} heapNode;

typedef struct PQ {
    heapNode* heap;
    int size;
} PQ;

void insert(heapNode aNode, heapNode* heap, int size) {
    int idx;
    heapNode tmp;

    idx = size + 1;
    heap[idx] = aNode;

    while (heap[idx].priority < heap[idx/2].priority && idx > 1) {
        tmp = heap[idx];
        heap[idx] = heap[idx/2];
        heap[idx/2] = tmp;
        idx /= 2;
    }
}

void shiftdown(heapNode* heap, int size, int idx) {
    int cidx;        //index for child
    heapNode tmp;

    for (;;) {
        cidx = idx*2;
        if (cidx > size) {
            break;   //it has no child
        }

        if (cidx < size) {
            if (heap[cidx].priority > heap[cidx+1].priority) {
                ++cidx;
            }
        }

        //swap if necessary
        if (heap[cidx].priority < heap[idx].priority) {
            tmp = heap[cidx];
            heap[cidx] = heap[idx];
            heap[idx] = tmp;
            idx = cidx;
        } else {
            break;
        }
    }
}

heapNode removeMin(heapNode* heap, int size) {
    int cidx;
    heapNode rv = heap[1];
    heap[1] = heap[size];
    --size;
    shiftdown(heap, size, 1);
    return rv;
}

void enqueue(heapNode node, PQ *q) {
    insert(node, q->heap, q->size);
    ++q->size;
}

heapNode dequeue(PQ *q) {
   heapNode rv = removeMin(q->heap, q->size);
   --q->size;
   return rv;
}

void initQueue(PQ *q, int n) {
   q->size = 0;
   q->heap = (heapNode*)malloc(sizeof(heapNode)*(n+1));
}

int main(int argc, char **argv) {
    int n;
    int i;
    PQ q;
    heapNode hn;

    n = atoi(argv[1]);

    initQueue(&q, n);

    srand(time(NULL));

    for (i = 0; i < n; ++i) {
        hn.value = rand() % 10000;
        hn.priority = rand() % 5 + 1;
        printf("enqueue node with value: %d and priority: %d\n", hn.value, hn.priority);
        enqueue(hn, &q);
    }

    printf("\ndequeue all values:\n");

    for (i = 0; i < n; ++i) {
        hn = dequeue(&q);
        printf("dequeued node with value: %d and priority: %d, queue size after removal: %d\n", hn.value, hn.priority, q.size);
    }
}