/* Atlas test: Astral solver — hard prune conditions
   Tests edge cases: pointer arithmetic comparisons within and across blocks,
   NULL arithmetic, and conditions that stress the translation layer.

   Expected:
   - test_offset_eq_same_block: if-branch taken (p+4 == q when q was assigned
     p+4, subst resolves), else-branch pruned
   - test_cross_block_offset: if-branch is theoretically reachable — when p is NULL,
     mid_p = p+8 = 0x8 which could fall within q's allocated block. Astral correctly
     reports SAT. Both branches survive
   - test_double_deref_alias: after *buf = p and q = *buf, q should alias p.
     if (q == p) should be always taken via subst
   - test_null_ptr_arith_eq: p = NULL, q = NULL. if (p == q) should be always
     taken (both null, structural equality after normalize)
   - test_four_allocs_ring: a -> b -> c -> d assignment chain via stores.
     After loading back, each loaded value should be distinct from the others
     (they point to separate allocations). Tests Astral with multiple spatial
     predicates and equality checks */

#include <stdlib.h>

void test_offset_eq_same_block() {
    char *p = (char *)malloc(16);
    char *q = p + 4;
    char *r = p + 4;
    if (q == r) {
        /* ALWAYS TAKEN: both are p+4, subst resolves identically */
        *q = 'Y';
    } else {
        /* UNREACHABLE */
        *q = 'N';
    }
    free(p);
}

void test_cross_block_offset() {
    char *p = (char *)malloc(16);
    char *q = (char *)malloc(16);
    char *mid_p = p + 8;
    if (mid_p == q) {
        /* THEORETICALLY REACHABLE: when p is NULL, mid_p = 0x8 which could
           fall within q's allocated block. Astral correctly reports SAT */
        *mid_p = 'X';
    } else {
        /* ALSO REACHABLE */
        *mid_p = 'A';
        *q = 'B';
    }
    free(p);
    free(q);
}

typedef struct node {
    struct node *ptr;
} node_t;

void test_double_deref_alias() {
    node_t *buf = (node_t *)malloc(sizeof(node_t));
    node_t *p = (node_t *)malloc(sizeof(node_t));
    buf->ptr = p;
    node_t *q = buf->ptr;
    if (q == p) {
        /* ALWAYS TAKEN: q loaded from buf->ptr which was stored as p */
        q->ptr = buf;
    } else {
        /* UNREACHABLE */
        q->ptr = NULL;
    }
    free(p);
    free(buf);
}

void test_null_ptr_arith_eq() {
    int *p = NULL;
    int *q = NULL;
    if (p == q) {
        /* ALWAYS TAKEN: both null, trivially equal */
        return;
    }
    /* UNREACHABLE */
}

void test_four_allocs_ring() {
    node_t *a = (node_t *)malloc(sizeof(node_t));
    node_t *b = (node_t *)malloc(sizeof(node_t));
    node_t *c = (node_t *)malloc(sizeof(node_t));
    node_t *d = (node_t *)malloc(sizeof(node_t));

    a->ptr = b;
    b->ptr = c;
    c->ptr = d;
    d->ptr = a;

    /* Load back the stored pointers */
    node_t *ab = a->ptr;
    node_t *bc = b->ptr;

    if (ab == bc) {
        /* UNREACHABLE: ab == b, bc == c, and b != c (separate allocs) */
        ab->ptr = NULL;
    } else {
        /* ALWAYS TAKEN */
        ab->ptr = d;
    }

    free(a);
    free(b);
    free(c);
    free(d);
}
