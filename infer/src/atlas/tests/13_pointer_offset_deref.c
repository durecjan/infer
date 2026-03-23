/* Atlas test: pointer arithmetic then dereference
   Expected: block splitting at the computed offset,
   pointer arithmetic produces (base + offset) expression,
   dereference checks bounds and creates ExpPointsTo cell */

#include <stdlib.h>

void pointer_offset_deref(char* buf) {
    //char *buf = (char *)malloc(16);
    char *mid = buf + 8;
    *mid = 'A';
    char c = *mid;
    free(buf);
}
