#include <stdlib.h>

/* Atlas test: formal pointer self-reference, offsetting, and free via offset.
   Exercises: self-reference (*p = p) on a formal, pointer arithmetic
   creating an alias, NULL stores to force Base/End reevaluation,
   and attempting free through an offset pointer (should fail). */

void formal_self_ref_offset_free(char **p) {
    *p = (char *)p;

    char **q = p + 1;
    *q = NULL;

    char *r = *p;
    *(char **)r = NULL;

    free(q);
}

// TODO: at line 11 (char **q = p + 1;) we do not translate to byte offset FIXME

/*
 * Expected error contracts:
 * NullPointerDeference -- *p = (char *)p; [line 9, column 5]
 * NullPointerDeference -- *q = NULL; [line 12, column 5]
 * [TERMINAL] NonBasePointerFree -- free(q); [line 17, column 5]
 */
