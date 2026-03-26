#ifndef QUEUE_H
#define QUEUE_H

#include <stdlib.h>
#include <string.h>

struct node {
    char *data;
    struct node *next;
};

struct queue {
    struct node *head;
    struct node *tail;
};

#endif
