#include <stdlib.h>

int main() {
    int* buf = malloc(8 * sizeof(int));
    if (buf == NULL) { return 1; }

    *buf = 7;               /* header: payload length */
    int* data = buf + 1;    /* payload starts after header */

    //...

    int len = *buf;
    for (int *p = data; p < data + len; p++) {
        *p = 0;
    }

    //...

    *(data + len) = -1;     /* BUG: access one past end of buf */

    //...

    free(buf);
    return 0;
}
