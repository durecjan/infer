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

/*
 * 36d does not work properlly, we need to rethink how to handle structures in memcpy
 */
