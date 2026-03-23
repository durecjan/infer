/* Atlas test: freeing a non-base pointer
   Expected: error state, offset from free call does not match
   the base constraint offset (free requires the original malloc pointer) */

#include <stdlib.h>

void free_non_base_pointer() {
    char *p = (char *)malloc(16);
    char *q = p + 4;
    free(q);
}
