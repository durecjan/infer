/* Atlas test: malloc, store a value, load it back
   Expected: clean state, ExpPointsTo for the cell with stored value,
   load variable substituted to the destination of the ExpPointsTo */

#include <stdlib.h>

void malloc_store_load() {
    int *p = (int *)malloc(sizeof(int));
    *p = 42;
    int x = *p;
    free(p);
}

// TODO for non pointer types, there is no need for Base, End constraints
//
// note: (p+0) -()-> Var(6) -- if we execute the same code within if else branches, then we get different cell ids
//
// note: postprocessing final state, clear locals, keep formals
