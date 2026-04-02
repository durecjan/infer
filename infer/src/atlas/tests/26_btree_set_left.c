#include "btree.h"

int tree_set_left(struct tnode *parent, int key) {
    if (parent->left != NULL) {
        free(parent->left);
    }

    struct tnode *n = (struct tnode *)malloc(sizeof(struct tnode));
    if (n == NULL) return -1;

    n->key = key;
    n->left = NULL;
    n->right = NULL;
    parent->left = n;
    return 0;
}

// TODO: when freeing block, case missing base, then infer size from type, also add missing End,  BlockPointsTo
// TODO: also rethink what kind of error contract this should produce

/*
 * CASE parent->left == NULL && n == NULL
 * Expected precondition:
 * (parent+4) -(8)-> (x1)
 * (Base(parent)<=parent+4) & (End(parent)>=parent+12) & (x1==null)
 * Expected postcondition:
 * (parent+4) -(8)-> (x1)
 * (n==null) & (Base(n)==0) & (End(n)==0) & (%ret==-1)
 *
 * CASE parent->left == NULL && n != NULL
 * Expected precondition:
 * (parent+4) -(8)-> (x1)
 * (Base(parent)<=parent+4) & (End(parent)>=parent+12) & (x1==null)
 * Expected postcondition:
 * (parent+4) -(8)-> (n) * (n+0) -(4)-> (y1) * (n+4) -(8)-> (y2) * (n+12) -(8)-> (y3) * (n+20) -(4)-> block
 * (Base(n)==n+0) & (End(n)==n+24) & (y1==key) & (y2==null) & (y3==null) & (%ret==0) & (Base(y2)==0) & (End(y2)==0) & (Base(y3)==0) & (End(y3)==0)
 *
 * CASE parent->left != NULL && n == NULL
 * Expected precondition:
 * (parent+4) -(8)-> (x1) * (x1) -(24)-> block
 * (Base(parent)<=parent+4) & (End(parent)>=parent+12) & (x1!=null) & (Base(x1)<=x1+0) & (End(x1)>=x1+24)
 * Expected postcondition:
 * (parent+4) -(8)-> (x1)
 * Freed(x1) & (n==null) & (Base(n)==0) & (End(n)==0) & (%ret==-1)
 *
 * CASE parent->left != NULL && n != NULL
 * Expected precondition:
 * (parent+4) -(8)-> (x1) * (x1) -(24)-> block
 * (Base(parent)<=parent+4) & (End(parent)>=parent+12) & (x1!=null) & (Base(x1)<=x1+0) & (End(x1)>=x1+24)
 * Expected postcondition:
 * (parent+4) -(8)-> (n) * (n+0) -(4)-> (y1) * (n+4) -(8)-> (y2) * (n+12) -(8)-> (y3) * (n+20) -(4)-> block
 * Freed(x1) & (Base(n)==n+0) & (End(n)==n+24) & (y1==key) & (y2==null) & (y3==null) & (%ret==0) & (Base(y2)==0) & (End(y2)==0) & (Base(y3)==0) & (End(y3)==0)
 *
 * Expected error contracts:
 * NullPointerDereference -- if (parent->left != NULL)  [line 4, column 9]
 * NonBasePointerFree     -- free(parent->left)         [line 5, column 9]
 */
