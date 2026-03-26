#include "queue.h"

char *dequeue(struct queue *q) {
    if (q->head == NULL) return NULL;

    struct node *n = q->head;
    char *data = n->data;

    q->head = n->next;
    if (q->head == NULL) {
        q->tail = NULL;
    }

    free(n);
    return data;
}
