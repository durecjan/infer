/* Atlas test: array element access via block splitting
   Expected: block split creates ExpPointsTo cells at array element offsets,
   accessing arr[0] and arr[2] should carve cells from the allocated block */

#include <stdlib.h>

void array_access() {
    int *arr = (int *)malloc(4 * sizeof(int));
    arr[0] = 100;
    arr[2] = 300;
    int x = arr[0];
    int y = arr[2];
    free(arr);
}
