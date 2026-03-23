/* Atlas test: basic malloc/free lifecycle
   Expected: clean state, Freed(p) in pure, block remains in spatial */

#include <stdlib.h>

void malloc_free_basic() {
    int *p = (int *)malloc(sizeof(int));
    free(p);
}

// TODO after added Freed, remove PointsTo predicates, Base, End constraints
