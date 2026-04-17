#include <stdlib.h>
#include <string.h>

/* TC 37: memcpy edge cases — overlap, zero size, symbolic size/offset */

/* 37a: zero-size memcpy — should behave as skip, no memory access
   Expected: single ok contract, ret = dst, no freed/bounds checks */
void test_zero_size(int *dst, int *src) {
	memcpy(dst, src, 0);
}

/* 37b: overlapping regions — same block, overlapping offsets
   Expected: error contract for overlapping memcpy (UB) */
void test_overlap() {
	int *buf = malloc(4 * sizeof(int));
	if (buf == NULL) return;
	buf[0] = 1;
	buf[1] = 2;
	buf[2] = 3;
	buf[3] = 4;
	/* src=[buf+0, buf+8), dst=[buf+4, buf+12) — overlap at [buf+4, buf+8) */
	memcpy(&buf[1], &buf[0], 2 * sizeof(int));
	free(buf);
}

/* 37c: non-overlapping same block — offsets far enough apart
   Expected: ok contract, no overlap error */
void test_no_overlap_same_block() {
	int *buf = malloc(4 * sizeof(int));
	if (buf == NULL) return;
	buf[0] = 10;
	buf[1] = 20;
	/* src=[buf+0, buf+4), dst=[buf+8, buf+12) — no overlap */
	memcpy(&buf[2], &buf[0], sizeof(int));
	free(buf);
}

/* 37d: symbolic size — size passed as parameter
   Expected: both zero and non-zero paths produced,
   Astral fallback may refine if size constraints exist */
/*
void test_symbolic_size(int *dst, int *src, int n) {
	memcpy(dst, src, n);
}
note: explodes within Astral
*/

/* 37e: use after free — src is freed before memcpy
   Expected: error contract for use-after-free on src */
void test_src_freed() {
	int *src = malloc(sizeof(int));
	int *dst = malloc(sizeof(int));
	if (src == NULL || dst == NULL) return;
	*src = 42;
	free(src);
	memcpy(dst, src, sizeof(int));
	free(dst);
}

/* 37f: null pointer — dst is null
   Expected: error contract for null dereference on dst */
void test_dst_null(int *src) {
	int *dst = NULL;
	memcpy(dst, src, sizeof(int));
}
