#include <stdlib.h>

/* TC 44: malloc(0) error contract
   Tests the new malloc-zero handling. check_size_zero classifies the
   size argument as provably zero / provably non-zero / indeterminate;
   exec_malloc_instr dispatches to exec_malloc_zero / _nonzero / _unknown
   accordingly. The unknown case mirrors `n != 0` (success/null branches)
   or `n == 0` (error branch) into both current and missing per the
   assume-as-assert principle. */

/* 44a: deterministic non-zero size — baseline.
   eval_expr_to_int64_opt folds the literal to 4. check_size_zero
   returns (false, true) → exec_malloc_nonzero.
   Expected: success + null-failure (one disjunct under --atlas-unsafe-malloc).
   No error branch. */
void test_malloc_concrete_nonzero() {
    int *p = malloc(4);
    if (p == NULL) return;
    *p = 42;
    free(p);
}

/* 44b: literal zero size — provably zero.
   check_size_zero returns (true, false) → exec_malloc_zero.
   Expected: one terminal error state with err_malloc_zero_size,
   no success or null-failure path. */
void test_malloc_concrete_zero() {
    int *p = malloc(0);
    /* unreachable past the malloc call on this branch */
    free(p);
}

/* 44c: variable assigned zero, then passed — eval_expr_to_int64_opt
   should resolve through the substitution and fold the size to 0.
   Same outcome as 44b: provably zero, single error state. */
void test_malloc_var_zero() {
    int n = 0;
    int *p = malloc(n);
    free(p);
}

/* 44d: unconstrained symbolic size — indeterminate.
   Both `size == 0` and `size != 0` are SAT under empty pure;
   check_size_zero returns (false, false) → exec_malloc_unknown.
   Expected: 3 disjuncts (2 with --atlas-unsafe-malloc):
     - success branch with `n != 0` mirrored to current+missing
     - null-failure branch with `n != 0` mirrored to current+missing
     - error branch with `n == 0` mirrored to current+missing
   The dereference *p = 0 should therefore only execute on the
   success branch where n != 0 is in scope. */
void test_malloc_symbolic(int n) {
    int *p = malloc(n);
    if (p == NULL) return;
    *p = 0;
    free(p);
}

/* 44e: symbolic size guarded positive — Astral should prove
   `n == 0` UNSAT given the `n > 0` constraint inserted by the
   prune handler. check_size_zero returns (false, true) →
   exec_malloc_nonzero, no error branch.
   Expected: success + null-failure only. */
void test_malloc_symbolic_positive(int n) {
    if (n > 0) {
        int *p = malloc(n);
        if (p == NULL) return;
        *p = 0;
        free(p);
    }
}

/* 44f: symbolic size guarded as exactly zero — Astral should
   prove `n != 0` UNSAT given the `n == 0` constraint from prune.
   check_size_zero returns (true, false) → exec_malloc_zero.
   Expected: one terminal error state, no allocation. */
void test_malloc_symbolic_zero_branch(int n) {
    if (n == 0) {
        int *p = malloc(n);
        free(p);
    }
}
