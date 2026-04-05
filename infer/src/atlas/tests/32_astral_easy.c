/* Atlas test: Astral solver — easy prune conditions
   Tests basic pointer equality/disequality that Astral can resolve
   via separating conjunction and aliasing.

   Expected:
   - test_distinct_allocs: if-branch pruned (p != q via spatial separation),
     only else-branch survives
   - test_alias_eq: else-branch pruned (p == q via subst), only if-branch survives
   - test_self_eq: else-branch pruned (p == p trivially), only if-branch survives
   - test_null_after_malloc_fail: on the malloc-fail path (p == NULL),
     if-branch taken; on success path (p != NULL), else-branch taken */

#include <stdlib.h>

void test_distinct_allocs() {
    int *p = (int *)malloc(sizeof(int));
    int *q = (int *)malloc(sizeof(int));
    if (p == q) {
        /* UNREACHABLE: two separate mallocs cannot return the same address
           (separating conjunction in Astral) */
        *p = 42;
    } else {
        *p = 1;
        *q = 2;
    }
    free(p);
    free(q);
}

void test_alias_eq() {
    int *p = (int *)malloc(sizeof(int));
    int *q = p;
    if (p == q) {
        /* ALWAYS TAKEN: q is an alias for p (subst resolves before Astral) */
        *q = 10;
    } else {
        /* UNREACHABLE */
        *q = 20;
    }
    free(p);
}

void test_self_eq() {
    int *p = (int *)malloc(sizeof(int));
    if (p == p) {
        /* ALWAYS TAKEN: trivially true */
        *p = 1;
    } else {
        /* UNREACHABLE */
        *p = 2;
    }
    free(p);
}

void test_null_after_malloc_fail() {
    int *p = (int *)malloc(sizeof(int));
    /* malloc returns two states: success (p != NULL) and fail (p == NULL) */
    if (p == NULL) {
        /* Taken only on fail path */
        return;
    }
    /* Only success path reaches here */
    *p = 42;
    free(p);
}
