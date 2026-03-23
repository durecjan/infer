/* Atlas test: malloc(0) then access
   Expected: error state, End bound equals Base (zero-size block),
   any dereference should fail bounds check */

#include <stdlib.h>

void malloc_zero_size() {
    int *p = (int *)malloc(0);
    *p = 42;
    free(p);
}
