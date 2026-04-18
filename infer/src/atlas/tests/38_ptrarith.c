#include <stdlib.h>

/* TC 38: pointer arithmetic bound checks */

/* 38a: formal pointer with prior access — deref establishes Base/End,
   then arithmetic goes beyond.
   Exercises ptrarith_with_missing_bound (Base/End already exist from deref).
   Expected: error below/above + ok with mutated bounds */
int *test_formal_with_bounds(int **arr) {
	int *first = *arr;
	int *third = &arr[2];
	return third;
}

/* 38b: formal pointer without prior access — no Base/End yet.
   Exercises ptrarith_create_missing_base_end.
   Expected: error null + error freed + error below + error above + ok */
void test_formal_no_bounds(int *p, int *end) {
	if (p + 1 != end) {
		*p = 42;
	}
}

/* 38c: local pointer arithmetic — malloc'd buffer, offset beyond allocation.
   Exercises ptrarith_with_bounds (concrete Base/End from malloc).
   Expected: error above end on buf+5 (past allocation) */
void test_local_oob() {
	int *buf = malloc(4 * sizeof(int));
	if (buf == NULL) return;
	int *last = &buf[3];
	int *oob = &buf[5];
	*last = 1;
	free(buf);
}
