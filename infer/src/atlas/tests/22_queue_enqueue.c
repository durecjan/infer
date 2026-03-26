#include "queue.h"

void enqueue(struct queue *q, char *data) {
    struct node *n = (struct node *)malloc(sizeof(struct node));
    if (n == NULL) return;

    n->data = data;
    n->next = NULL;

    if (q->tail == NULL) {
        q->head = n;
        q->tail = n;
    } else {
        q->tail->next = n;
        q->tail = n;
    }
}
