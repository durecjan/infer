/* Atlas test: formal pointer parameter free
   Expected: missing Base constraint generated,
   Freed added to current pure */

#include <stdlib.h>

void formal_pointer_free(int *p) {
    free(p);
}
/*
	note:
	here we generate only one error contract - missing base constraint
	we could add a check for missing end constraint, also for heap predicate source
*/
