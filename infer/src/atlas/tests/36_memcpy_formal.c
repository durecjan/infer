#include <stdlib.h>
#include <string.h>

/* TC 36: memcpy with formal (caller-allocated) pointers
   Tests precondition generation — both src and dest come from caller */

/* 36a: basic formal-to-formal copy
   Expected: ok contract requires Base/End bounds for both params,
   error contracts for freed/null/out-of-bounds on both */
void test_formal_copy(int *dst, int *src) {
	memcpy(dst, src, sizeof(int));
}

/* 36b: formal src, local dest
   Expected: ok contract requires bounds on src only,
   dest is locally allocated so no precondition needed for it */
void test_formal_src_local_dest(int *src) {
	int *dst = malloc(sizeof(int));
	if (dst == NULL) return;
	memcpy(dst, src, sizeof(int));
	free(dst);
}

/* 36c: copy struct via formal pointers
   Expected: ok contract requires bounds for sizeof(struct pair) on both */
struct pair { int a; int b; };

void test_formal_struct_copy(struct pair *dst, struct pair *src) {
	memcpy(dst, src, sizeof(struct pair));
}

/* 36d: partial copy from formal — only first field
   Expected: bounds check uses sizeof(int) not sizeof(struct pair) */
void test_formal_partial_copy(struct pair *dst, struct pair *src) {
	memcpy(dst, src, sizeof(int));
}

/* 36e: cross-struct boundary copy — last field of struct[0], whole struct[1],
   first field of struct[2]. Copies 3 fields across struct boundaries.
   Expected: struct-aware chopping produces 3 cells of sizes 4, 4, 4
   (pair.b from src[0], pair.a + pair.b from src[1], pair.a from src[2]) */
struct triple { int x; int y; int z; };

void test_cross_struct_copy(struct triple *dst, struct triple *src) {
	/* src+4 is offset of field y in first struct, copy 3 fields = 12 bytes */
	memcpy(&(dst->y), &(src->y), 3 * sizeof(int));
}

/* 36f: formal struct memcpy with prior field access — fields are accessed
   before the copy, so ExpPointsTo already exist and should be preserved.
   Expected: existing ExpPointsTo pass through, BlockPointsTo regions get chopped */
void test_formal_struct_prior_access(struct pair *dst, struct pair *src) {
	src->a = 10;
	dst->b = 20;
	memcpy(dst, src, sizeof(struct pair));
}

/* 36g: type mismatch — src is struct pair (2 ints = 8 bytes),
   dest is long* (1 long = 8 bytes). Same total size, different field layout.
   Expected: src gets struct-aware chopping (4+4), dest gets uniform 8-byte cells */
void test_type_mismatch(long *dst, struct pair *src) {
	memcpy(dst, src, sizeof(struct pair));
}
