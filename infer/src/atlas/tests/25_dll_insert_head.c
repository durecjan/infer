#include "dlist.h"

void dll_insert_head(struct dlist *dl, int val) {
    struct dnode *n = (struct dnode *)malloc(sizeof(struct dnode));
    if (n == NULL) return;

    n->val = val;
    n->prev = NULL;
    n->next = dl->head;

    if (dl->head != NULL) {
        dl->head->prev = n;
    }
    dl->head = n;
}

/*
 * Ok case n == NULL
 * Expected precondition:
 * Expected postcondition:
 * (n==null) & (Base(n)==0) & (End(n)==0)
 *
 * Ok case n!= NULL && dl->head == NULL
 * Expected precondition:
 * (dl+0) -(8)-> x1
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (x1==null)
 * Expected postcondition:
 * (dl+0) -(8)-> x5 * (n+0) -(4)-> x2 * (n+4) -(8)-> x3 * (n+12) -(8)-> x4 * (n+20) -(4)-> block
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (x1==null) & (Base(n)==n+0) & (End(n)==n+24) & (x2==val) & (x3==null) & (Base(x3)==0) & (End(x3)==0) & (x4==x1) & (x5==n)
 *
 * Error case n!= NULL && dl->head == NULL
 * [line 9] Expected precondition:
 * (Base(q)>q+0)
 * [line 9] Expected precondition:
 * (End(q)<q+8)
 * [line 9] Expected precondition:
 * Freed(q)
 *
 * Ok case n!=NULL && dl->head != NULL
 * Expected precondition:
 * (dl+0) -(8)-> x1 * (x1+4) -(8)-> x2
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (Base(x1)<=x1+4) & (End(x1)>=x1+12) & (x1!=null)
 * Expected postcondition:
 * (dl+0) -(8)-> x3 * (x1+4) -(8)-> x4 * (n+0) -(4)-> x5 * (n+4) -(8)-> x6 * (n+12) -(8)-> x7 * (n+20) -(4)-> block
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (Base(x1)<=x1+4) & (End(x1)>=x1+12) & (x1!=null) & (Base(n)==n+0) & (End(n)==n+24) & (x5==val) & (x6==null) & (Base(x6)==0) & (End(x6)==null) & (x7==x1) & (x3==n) & (x4==n)
 *
 * Error case n!= NULL && dl->head != NULL
 * [line 9] Expected precondition:
 * (Base(q)>q+0)
 * [line 9] Expected precondition:
 * (End(q)<q+8)
 * [line 9] Expected precondition:
 * Freed(q)
 * [line 12] Expected precondition:
 * (dl+0) -(8)-> x1
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (x1!=null) & (Base(x1)>x1+4)
 * [line 12] Expected precondition:
 * (dl+0) -(8)-> x1
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (x1!=null) & (End(x1)<x1+12)
 * [line 12] Expected precondition:
 * (dl+0) -(8)-> x1
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & (x1!=null) & Freed(x1)
 *
 */
