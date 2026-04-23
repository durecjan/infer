#include <stdlib.h>

/* TC 40: symbolic size support
   Tests correct handling of malloc/Base/End with symbolic (formal) sizes */

/* 40a: local malloc with symbolic size, concrete access
   Expected: deref_raise_end_bound should NOT produce a terminal error —
   End(x) = x + n is symbolic, access at offset 4 may or may not exceed it.
   Current bug: eval_expr_offset defaults to 0 for symbolic End, so access_end > 0
   always holds, incorrectly entering the error+ok branch with wrong gap size */
void test_symbolic_size_access(int n) {
	char *x = malloc(n);
	if (x == NULL) return;
	x[4] = 'A';
	free(x);
}

/* 40b: pointer shift after malloc — base becomes negative relative to pointer
   After x = &(*x + 1), x points one element past allocation start.
   Base(x) = x - sizeof(int), a negative offset.
   Tests whether deref_check_base handles symbolic base correctly when
   the pointer has been shifted forward within its own block */
void test_shifted_pointer_base(int n) {
	int *x = malloc(n * sizeof(int));
	if (x == NULL) return;
	x = x + 1;
	*x = 42;
	free(x - 1);
}

/* 40c: symbolic size with conditional access — upper bound stress test
   Allocation of n ints, guarded accesses at various offsets.
   if (n > 1): ptr[1] = 42 — Astral should prove 8 <= n*4 given n > 1
   if (n <= 2): ptr[3] = 3 — should error: n <= 2 means n*4 <= 8, but access at 12+4=16
   Tests symbolic End check with Astral using narrowed constraints from prune */
void test_symbolic_upper_bound(int n) {
	int *p = malloc(n * sizeof(int));
	if (p == NULL) return;
	if (n > 1) {
		p[1] = 42;
	}
	if (n <= 2) {
		p[3] = 3;
	}
	free(p);
}

/* 40d: symbolic size with pointer shift and conditional access — lower bound stress test
   Allocation of n ints, shift pointer forward by 2, then guarded accesses.
   After p = p + 2, p points to original_base + 8.
   if (n > 3): p[1] = 42 — access at fresh+8+4=12, Astral should prove 12 <= n*4 given n > 3
   if (n <= 2): p[-3] = 3 — access at fresh+8-12=fresh-4, below Base(fresh)=0, should error
   Tests symbolic bounds with shifted pointer and negative indexing */
void test_symbolic_lower_bound(int n) {
	int *p = malloc(n * sizeof(int));
	if (p == NULL) return;
	p = p + 2;
	if (n > 3) {
		p[1] = 42;
	}
	if (n <= 2) {
		p[-3] = 3;
	}
	free(p - 2);
}
