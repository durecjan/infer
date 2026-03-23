/* Atlas test: dereference of unallocated pointer
   Expected: error state, Base(p)==0 and End(p)==0 from declaration
   means no memory is allocated, dereference check catches this immediately
   (not as a missing resource but as a definite error) */

#include <stdlib.h>

void unallocated_deref() {
    int *p;
    *p = 42;
}

/*
	there is no VariableLifetimeBegins sil instruction, hence we do not catch this
	rethink adding constraints of local variables somewhere else (state initialization)
*/
