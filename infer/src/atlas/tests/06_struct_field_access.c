/* Atlas test: struct field access via block splitting
   Expected: block split into ExpPointsTo cells at field offsets,
   each field access carves a cell from the BlockPointsTo */

#include <stdlib.h>

struct point {
    int x;
    int y;
};

void struct_field_access() {
    struct point *p = (struct point *)malloc(sizeof(struct point));
    p->x = 10;
    p->y = 20;
    int a = p->x;
    int b = p->y;
    free(p);
}
