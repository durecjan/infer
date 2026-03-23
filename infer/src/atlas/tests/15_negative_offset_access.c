/* Atlas test: negative offset memory access
   Expected: error state, dereference_check_base catches
   offset < Base bound */

#include <stdlib.h>

void negative_offset_access() {
    int *p = (int *)malloc(4 * sizeof(int));
    int x = *(p - 1);
    free(p);
}
