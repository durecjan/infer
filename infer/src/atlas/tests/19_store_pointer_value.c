/* Atlas test: storing a pointer value through dereference
   Expected: store_dereference_address_assign path taken,
   substitution map updated to link the destination to the stored pointer */

#include <stdlib.h>

void store_pointer_value() {
    int **pp = (int **)malloc(sizeof(int *));
    int *q = (int *)malloc(sizeof(int));
    *pp = q;
    int *r = *pp;
    *r = 99;
    free(q);
    free(pp);
}
