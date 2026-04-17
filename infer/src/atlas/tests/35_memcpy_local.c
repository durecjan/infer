#include <stdlib.h>

void memcpy_test() {
	
	int* x = malloc(sizeof(int));
	if (x == NULL) return;
	int* y = malloc(sizeof(int));
	if (y == NULL) {
		free(x);
		return;
	}

	*x = 42;
	memcpy(y, x, sizeof(int));
	free(x);
	free(y);
}
