#include<stdlib.h>

void test_a() {
    int i = 0;
    i++;
}

void test_b() {
    int* x = malloc(sizeof(int));
    if (x == NULL) return;
    *x = 0;
    *x = *x + 1;
    free(x);
}
