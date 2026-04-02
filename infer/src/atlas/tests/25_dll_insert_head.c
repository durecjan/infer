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

// TODO: there should not be a return variable
// TODO: currently, we add (Base(x)<=x+0) instead of (Base(x)<=x+4) on line 12

/*
 * CASE if(n == NULL)
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * (n==null) & (Base(n)==0) & (End(n)==0)
 *
 * CASE if (dl->head == NULL)
 * Expected precondition:
 * (dl+0) -(8)-> ([z1])
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & ([z1]==null)
 * Expected postcondition:
 * if (dl->head == NULL)
 * (dl+0) -(8)-> (n) * (n+0) -(4)-> (val) * (n+4) -(8)-> (x1) * (n+12) -(8)-> ([z1]) * (n+20) -(4)-> block
 * (Base(n)==n) & (End(n)==n+24) & (x1==null) & (Base(x1)==0) & (End(x1)==0)
 *
 * CASE if (dl->head != NULL)
 * Expected precondition:
 * (dl+0) -(8)-> ([z1]) * ([z1]+4) -(8)-> (y1)
 * (Base(dl)<=dl+0) & (End(dl)>=dl+8) & ([z1]!=null) & (Base([z1])<=[z1]+4) & (End([z1])>=[z1]+12)
 * * Expected postcondition:
 * if (dl->head != NULL)
 * (dl+0) -(8)-> (n) * (n+0) -(4)-> (val) * (n+4) -(8)-> (x1) * (n+12) -(8)-> ([z1]) * (n+20) -(4)-> block * ([z1]+4) -(8)-> (n)
 * (Base(n)==n) & (End(n)==n+24) & (x1==null) & (Base(x1)==0) & (End(x1)==0)
 *
 *
 * Expected error contracts:
 * NullPointerDereference -- n->next = dl->head; [line 9, column 15]
 * NullPointerDereference -- dl->head->prev = n; [line 12, colum 9]
 */
