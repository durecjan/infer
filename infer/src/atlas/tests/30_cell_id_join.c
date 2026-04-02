#include <stdlib.h>

/* Atlas test: cell id join at branch merge.
   Both branches dereference the same malloc'd block and store the same value,
   producing states with different cell ids for the same logical cell.
   Demonstrates the limitation of structural equality in Domain.join —
   the two states are semantically identical but have different fresh ids,
   so join does not deduplicate them. */

int cell_id_join(int flag) {
    int *p = (int *)malloc(sizeof(int));
    if (p == NULL) return -1;

    if (flag > 0) {
        *p = 42;
    } else {
        *p = 42;
    }

    int val = *p;
    free(p);
    return val;
}

// TODO: expected does not match actual states - modify join to deduplicate cell identifiers
// note: state A has missing: (flag>0) and current: (Freed(p) & (Var(11)==42))
// note: state B has missing: !(flag>0) and current: (Freed(p) & (Var(13)==42))

/*
 * CASE p == NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * (p==null) & (Base(p)==0) & (End(p)==0) & (%ret==-1)
 *
 * CASE p != NULL
 * Expected precondition:
 * <empty>
 * <empty>
 * Expected postcondition:
 * <empty>
 * Freed(p) & (val==42) & (%ret==val)
 *
 * Expected error contracts:
 * <empty>
 */
