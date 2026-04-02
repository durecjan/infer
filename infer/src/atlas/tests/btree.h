#ifndef BTREE_H
#define BTREE_H

#include <stdlib.h>

struct tnode {
    int key;
    struct tnode *left;
    struct tnode *right;
};

#endif
