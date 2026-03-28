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

/*
 * Should produce exactly three OK final states:
 * 1) q->head == NULL
 *      missing.spatial: (q) -(8)-> (x1)
 *      missing.pure: (Base(q)<=q) & (End(q)>=(q+8)) & (x1==null)
 *      current.spatial:
 *      current.pure: (Base(%ret)==0) & (End(%ret)==0) & (%ret==null)
 *
 * 2) q->head != NULL && q->head->next == NULL
 *      missing.spatial: (q) -(8)-> (x2) * (q+8) -(8)-> (x3) * (x2) -(8)-> (x4) * (x2+8) -(8)-> (x5)
 *      missing.pure: (Base(q)<=q) & (End(q)>=q+16) & (x2!=null) & (Base(x2)<=x2) & (End(x2)>=x2+16) & (x5==null)
 *      current.spatial: (q) -(8)-> (x5) * (q+8) -(8)-> (x6)
 *      current.pure: Freed(x2) & (x6==null) & (Base(x6)==0) & (End(x6)==0) & (%ret==x4)
 *
 * 3) q->head != NULL && q->head->next != NULL
 *      missing.spatial: (q) -(8)-> (x7) * (x7) -(8)-> (x8) * (x7+8) -(8)-> (x9)
 *      missing.pure: (Base(q)<=q) & (End(q)>=q+16) & (x7!=null) & (Base(x7)<=x7) & (End(x7)>=x7+16) & (x9!=null)
 *      current.spatial: (q) -(8)-> (x9)
 *      current.pure: Freed(x7) & (%ret==x8)
 *
 * and exactly four ERROR states:
 * NullPointerDereference -- if (q->head == NULL) [line 4, column 9]
 * NullPointerDereference -- char *data = n->data; [line 7, column 18]
 * NullPointerDereference -- q->head = n->next; [line 9, column 15]
 * NullPointerDereference -- q->tail = NULL; [line 11, column 9]
 */
