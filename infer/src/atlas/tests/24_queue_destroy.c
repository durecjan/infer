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


/*
 * Ok: case q->head == NULL
 * Expected precondition:
 * (q + 0) -(8)-> x1 * (q + 8) -(8)-> x2
 * (Base(q)<=q) & (End(q)>=q+16) & (x1==null)
 * Expected postcondition:
 * (q + 0) -(8)-> x3 * (q + 8) -(8)-> x4
 * (Base(q)<=q) & (End(q)>=q+16) & (x3==null) & (Base(x3)==0) & (End(x3)==0) & (x4==null) & (Base(x4)==0) & (End(x4)==0)
 *
 * Ok: case q->head != NULL & q->head->data != NULL & q->head->next == NULL
 * Expected precondition:
 * (q + 0) -(8)-> x1 * (q + 8) -(8)-> x2 * (x1 + 0) -(8)-> x3 * (x1 + 8) -(8)-> x4 * (x3 + 0) -(1)-> block
 * (Base(q)<=q) & (End(q)>=q+16) & (x1!=null) & (Base(x1)==x1) & (End(x1)>=x1+16) & (Base(x3)==x3) & (End(x3)>=x3+1) & (x4==null)
 * Expected postcondition:
 * (q + 0) -(8)-> x5 * (q + 8) -(8)-> x6
 * (Base(q)<=q) & (End(q)>=q+16) & (x1!=null) & Freed(x1) & Freed(x3) & (x4==null) & (x5==null) & (Base(x5)==0) & (End(x)==0) & (x6==null) & (Base(x6)==0) & (End(x6)==0)
 *
 * Error: case q->head == NULL
 * [line 4] Expected precondition:
 * (Base(q)>q)
 * [line 4] Expected precondition:
 * (End(q)<q+8)
 * [line 4] Expected precondition:
 * Freed(q)
 * [line 12] Expected precondition:
 * (q + 0) -(8)-> x1
 * (Base(q)<=q) & (End(q)>=q+8) & (x1==null) & (End(q)<q+16)
 *
 * Error: case q->head != NULL & q->head->data != NULL & q->head->next == NULL
 * [line 4] Expected precondition:
 * (Base(q)>q)
 * [line 4] Expected precondition:
 * (End(q)<q+8)
 * [line 4] Expected precondition:
 * Freed(q)
 * [line 6] Expected precondition:
 * (q + 0) -(8)-> x1
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Base(x1)>x1+8)
 * [line 6] Expected precondition:
 * (q + 0) -(8)-> x1
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (End(x1)<x1+16)
 * [line 6] Expected precondition:
 * (q + 0) -(8)-> x1
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Freed(x1))
 * [line 7] Expected precondition:
 * (q + 0) -(8)-> x1 * (x1 + 8) -(8)-> x2
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Base(x1)<=x1+8) & (End(x1)>=x1+16) & (Base(x1)>x1)
 * [line 7] Expected precondition:
 * (q + 0) -(8)-> x1 * (x1 + 8) -(8)-> x2 * (x1 + 0) -(8)-> x3
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Base(x1)<=x1) & (End(x1)>=x1+16) & (Base(x3)!=x3)
 * [line 8] Expected precondition:
 * (q + 0) -(8)-> x1 * (x1 + 8) -(8)-> x2 * (x1 + 0) -(8)-> x3
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Base(x1)<=x1) & (End(x1)>=x1+16) & (Base(x3)==x3) & (End(x3)>=x3+1) & (Base(x1)!=x1)
 * [line 12] Expected precondition:
 * (q + 0) -(8)-> x1 * (x1 + 8) -(8)-> x2 * (x1 + 0) -(8)-> x3
 * (Base(q)<=q) & (End(q)>=q+8) & (x1!=null) & (Base(x1)==x1) & (End(x1)>=x1+16) & (Base(x3)==x3) & (End(x3)>=x3+1) & (x2==null) & (End(q)<q+16)
 */
