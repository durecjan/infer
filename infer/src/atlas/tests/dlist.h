#ifndef DLIST_H
#define DLIST_H

#include <stdlib.h>

struct dnode {
    int val;
    struct dnode *prev;
    struct dnode *next;
};

struct dlist {
    struct dnode *head;
    struct dnode *tail;
};

#endif
