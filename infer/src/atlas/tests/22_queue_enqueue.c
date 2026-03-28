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

/*
 * Should produce exactly three OK final states:
 * 1) n == NULL
 *
 * 2) n != NULL && q->tail == NULL
 *      missing.spatial: (q) -(8)-> (x1) * (q+8) -(8)-> (x2)
 *      missing.pure: (Base(q)<=q) & (End(q)>=(q+16)) & (x2==null)
 *      current.spatial: (q) -(8)-> (n) * (q+8) -(8)-> (n) * (n) -(8)-> (data) * (n+8) -(8)-> (x3)
 *      current.pure: (Base(n)==n) & (End(n)==n+16) & (x3==null) & (Base(x3)==0) & (End(x3)==0)
 *
 * 3) n!= NULL && q->tail != NULL
 *      missing.spatial: (q+8) -(8)-> (x4) * (x4+8) -(8)-> x5
 *      missing.pure: (Base(q)<=q) & (End(q)>=(q+16)) & (x4!=null) & (Base(x4)<=x4) & (End(x4)>=x4+16)
 *      current.spatial: (q+8) -(8)-> (n) * (n) -(8)-> (data) * (n+8) -(8)-> (x6) * (x4+8) -(8)-> (n)
 *      current.pure: (Base(n)==n) & (End(n)==n+16) & (x6==null) & (Base(x6)==0) & (End(x6)==0)
 *
 * and exactly three ERROR states:
 * NullPointerDereference -- if (q->tail == NULL) [line 10, column 9]
 * NullPointerDereference -- q->head = n; [line 11, column 9]
 * NullPointerDereference -- q->tail->next = n; [line 14, column 9]
 */
