/* Atlas test: Astral solver — medium prune conditions
   Tests pointer equality/disequality involving pointer arithmetic,
   multiple allocations, and transitive aliasing.

   Expected:
   - test_offset_neq_base: if-branch pruned (p+4 != p since offset 4 != 0,
     Astral sees distinct terms within the same block), else-branch survives
   - test_three_allocs_pairwise: all three equality checks should be pruned
     (three separate allocations are pairwise distinct), only the final
     else-else-else path survives with all three stores
   - test_transitive_alias: else-branch pruned (r == p because r = q and q = p,
     subst chain resolves structurally), if-branch survives
   - test_realloc_pattern: after free(p) + new malloc(q), p == q should be
     Unknown (freed pointer, new allocation could reuse address) — both
     branches survive conservatively */

#include <stdlib.h>

void test_offset_neq_base() {
    char *p = (char *)malloc(16);
    char *q = p + 4;
    if (q == p) {
        /* UNREACHABLE: p+4 != p (Astral can determine from arithmetic) */
        *q = 'X';
    } else {
        /* ALWAYS TAKEN */
        *p = 'A';
        *q = 'B';
    }
    free(p);
}

void test_three_allocs_pairwise() {
    int *a = (int *)malloc(sizeof(int));
    int *b = (int *)malloc(sizeof(int));
    int *c = (int *)malloc(sizeof(int));
    if (a == b) {
        /* UNREACHABLE: separate allocations */
        *a = 0;
    } else if (b == c) {
        /* UNREACHABLE: separate allocations */
        *b = 0;
    } else if (a == c) {
        /* UNREACHABLE: separate allocations */
        *c = 0;
    } else {
        /* ALWAYS TAKEN */
        *a = 1;
        *b = 2;
        *c = 3;
    }
    free(a);
    free(b);
    free(c);
}

void test_transitive_alias() {
    int *p = (int *)malloc(sizeof(int));
    int *q = p;
    int *r = q;
    if (r == p) {
        /* ALWAYS TAKEN: r -> q -> p via subst chain */
        *r = 42;
    } else {
        /* UNREACHABLE */
        *r = 0;
    }
    free(p);
}

void test_realloc_pattern() {
    int *p = (int *)malloc(sizeof(int));
    free(p);
    int *q = (int *)malloc(sizeof(int));
    if (p == q) {
        /* UNKNOWN: freed pointer, new alloc could reuse address.
           Astral may or may not resolve this — both branches
           should survive conservatively */
        *q = 1;
    } else {
        *q = 2;
    }
    free(q);
}
