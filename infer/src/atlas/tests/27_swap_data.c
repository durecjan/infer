#include "queue.h"

void swap_data(struct node *a, struct node *b) {
    char *tmp = a->data;
    a->data = b->data;
    b->data = tmp;
}

/*
 * Expected precondition:
 * (a+0) -(8)-> (x1) * (b+0) -(8)-> (x2)
 * (Base(a)<=a+0) & (End(a)>=a+8) & (Base(b)<=0) & (End(b)>=b+8)
 * Expected postcondition:
 * (a+0) -(8)-> (x2) * (b+0) -(8)-> (x1)
 * (tmp==x1)
 *
 *
 * Expected error contracts:
 * NullPointerDereference -- char *tmp = a->data; [line 4]
 * NullPointerDereference -- a->data = b->data; [line 5]
 */
