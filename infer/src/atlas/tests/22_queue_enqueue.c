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

// TODO: when adding prune condition to missing, needs to be added to current as well
// TODO: same applies for Base, End constraints
// TODO: NullPointerDereference should be split into two error contracts, one containing Base(q)>q and the other containing End(q)<q+8 (which includes Base(q)==0) -- in missing

/*
 * Should produce exactly three OK final states:
 * 1) n == NULL
 *
 * 2) n != NULL && q->tail == NULL
 *      missing.spatial: (q) -(8)-> (x1) * (q+8) -(8)-> (x2)
 *      missing.pure: (Base(q)<=q) & (End(q)>=(q+16)) & (x2==null)
 *      current.spatial: (q) -(8)-> (n) * (q+8) -(8)-> (n) * (n) -(8)-> (data) * (n+8) -(8)-> (x3)
 *      current.pure: (Base(q)<=q) & (End(q)>=(q+16)) & (Base(n)==n) & (End(n)==n+16) & (x3==null) & (Base(x3)==0) & (End(x3)==0) & (x2==null)
 *
 * 3) n!= NULL && q->tail != NULL
 *      missing.spatial: (q+8) -(8)-> (x4) * (x4+8) -(8)-> x5
 *      missing.pure: (Base(q)<=q+8) & (End(q)>=(q+16)) & (x4!=null) & (Base(x4)<=x4+8) & (End(x4)>=x4+16)
 *      current.spatial: (q+8) -(8)-> (n) * (n) -(8)-> (data) * (n+8) -(8)-> (x6) * (x4+8) -(8)-> (n)
 *      current.pure: (Base(q)<=q+8) & (End(q)>=(q+16)) & (Base(n)==n) & (End(n)==n+16) & (x6==null) & (Base(x6)==0) & (End(x6)==0) & (Base(x4)<=x4+8) & (End(x4)>=x4+16) & (x4!=null)
 *
 * and exactly three ERROR states:
 * NullPointerDereference -- if (q->tail == NULL) [line 10, column 9]
 * NullPointerDereference -- q->head = n; [line 11, column 9]
 * NullPointerDereference -- q->tail->next = n; [line 14, column 9]
 */
