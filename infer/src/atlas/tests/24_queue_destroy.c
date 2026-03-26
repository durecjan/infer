#include "queue.h"

void destroy(struct queue *q) {
    struct node *curr = q->head;
    while (curr != NULL) {
        struct node *next = curr->next;
        free(curr->data);
        free(curr);
        curr = next;
    }
    q->head = NULL;
    q->tail = NULL;
}
