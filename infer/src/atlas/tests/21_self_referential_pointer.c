/* Atlas test: self-referential pointer store (*p = p)
   Expected: store_dereference_address_assign path taken,
   the new ExpPointsTo source must be updated via expr_replace
   to use the fresh destination id instead of the original expression,
   ensuring consistency after substitution */

#include <stdlib.h>

void self_referential_pointer() {
    int **p = (int **)malloc(sizeof(int *));
    *p = (int *)p;
    int *q = *p;
    free(p);
}
