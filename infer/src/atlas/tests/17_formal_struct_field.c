/* Atlas test: formal pointer to struct with field access
   Expected: missing resources for Base, End, and the accessed cell,
   block splitting generates the missing ExpPointsTo for the field */

#include <stdlib.h>

struct pair {
    int first;
    int second;
};

void formal_struct_field(struct pair *p) {
    p->first = 1;
    p->second = 2;
}

/*
	note: again, too many error contracts i think
*/

// TODO if formal is struct * then add Base, End constraints to state on initialization (using Tenv)
