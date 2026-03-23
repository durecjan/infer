/* Atlas test: pointer aliasing
   Expected: substitution map links q to p's canonical id,
   both p and q refer to the same memory block,
   free via q should succeed (same base pointer) */

#include <stdlib.h>

void pointer_alias() {
    int *p = (int *)malloc(sizeof(int));
    int *q = p;
    *q = 42;
    int x = *p;
    free(q);
}
