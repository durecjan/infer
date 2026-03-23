/* Atlas test: formal pointer parameter dereference
   Expected: missing resources generated for Base and End constraints,
   missing ExpPointsTo for the accessed cell,
   biabduction infers the precondition for the caller */

#include <stdlib.h>

void formal_pointer_deref(int *p) {
    *p = 42;
    int x = *p;
}

// note: we generate too many error contracts
// TODO Base(p) <= p ; End(p) >= p + 4 -- modify Base End constraints and checks to handle this
