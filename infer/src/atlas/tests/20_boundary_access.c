/* Atlas test: access at exact boundary of allocated block
   Expected: clean state, accessing the last valid element
   should pass both Base and End checks */

#include <stdlib.h>

void boundary_access() {
    int *arr = (int *)malloc(4 * sizeof(int));
    arr[0] = 1;
    arr[3] = 4;
    int first = arr[0];
    int last = arr[3];
    free(arr);
}

/*	
   BUG
   again we mistakenly convert the size of type in the Lindex case

   [SIL_INSTR_LHS]: Lindex(Var(n$6), Const(Cint(3)))
   converted to
   [LHS_EXPR]: (arr+(3*8))

   expected behavior: convert to (arr+(3*4))
*/
