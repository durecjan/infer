#include <stdlib.h>

int main() {
	char* p = malloc(8 * sizeof(char));
	if (p == NULL) { return 1; }

	char* q = &p[8];  // advance pointer +1 past end (legal)
	
	*q = 42;  // BUG

	free(p);
	return 0;
}
