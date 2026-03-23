/* Atlas test: out-of-bounds memory access
   Expected: error state, dereference_check_end catches
   offset + cell_size > End bound */

#include <stdlib.h>

void out_of_bounds_access() {
    int *p = (int *)malloc(sizeof(int));
    int x = *(p + 1);
    free(p);
}
