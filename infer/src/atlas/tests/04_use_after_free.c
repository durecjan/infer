/* Atlas test: use after free detection
   Expected: error state on dereference after free,
   dereference_check_freed catches the Freed constraint */

#include <stdlib.h>

void use_after_free() {
    int *p = (int *)malloc(sizeof(int));
    *p = 10;
    free(p);
    int x = *p;
}
