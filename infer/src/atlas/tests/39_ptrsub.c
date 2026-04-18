#include <stdlib.h>

/* TC 39: pointer subtraction (MinusPP) checks */

/* 39a: ptrsub_base_found_same — same block, Base/End exist from prior access.
   Expected: ok (same canonical variable, non-null base) */
void test_base_found_same() {
	int *buf = malloc(4 * sizeof(int));
	if (buf == NULL) return;
	buf[0] = 1;
	buf[3] = 4;
	long diff = &buf[3] - &buf[0];
	free(buf);
}

/* 39b: ptrsub_base_found_diff — different variables, Base/End exist for LHS.
   Expected: error (y outside x's block) or ok (y within x's block) */
void test_base_found_diff() {
	int *buf = malloc(4 * sizeof(int));
	if (buf == NULL) return;
	buf[0] = 1;
	int *other = malloc(sizeof(int));
	if (other == NULL) { free(buf); return; }
	*other = 2;
	long diff = buf - other;
	free(buf);
	free(other);
}

/* 39c: ptrsub_no_base_same — same formal, no prior access.
   Expected: err_freed + err_null + ok (Base!=0 & End!=0) */
long test_no_base_same(int *p) {
	return p - p;
}

/* 39d: ptrsub_no_base_diff — different formals, no prior access.
   Expected: err_freed + err_below + err_above + ok (Base(x)<=y<=End(x)) */
long test_no_base_diff(int *a, int *b) {
	return a - b;
}
