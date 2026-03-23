/* Atlas test: double free detection
   Expected: error state on second free, Freed constraint already present */

#include <stdlib.h>

void double_free() {
    int *p = (int *)malloc(sizeof(int));
    free(p);
    free(p);
}
