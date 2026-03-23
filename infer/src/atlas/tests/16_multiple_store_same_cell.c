/* Atlas test: overwriting the same memory cell
   Expected: second store should match existing ExpPointsTo (exact match),
   destination gets a fresh id with the new value */

#include <stdlib.h>

void multiple_store_same_cell() {
    int *p = (int *)malloc(sizeof(int));
    *p = 10;
    *p = 20;
    int x = *p;
    free(p);
}

/*
	note:
	(Var(6)==10) stays in the state, but is no longer reachable via any program variable
*/
