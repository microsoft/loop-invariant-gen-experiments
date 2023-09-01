#include "assert.h"
int main() {
    int n = __VERIFIER_nondet_int();
    int m = __VERIFIER_nondet_int();
    int k = 0;
    int i,j;
    if (!(LARGE_INT <= n && n <= LARGE_INT)) return 0;
    if (!(LARGE_INT <= m && m <= LARGE_INT)) return 0;
    for (i = 0; i < n; i++) {
	for (j = 0; j < m; j++) {
	    k ++;
	}
    }
    __VERIFIER_assert(k >= LARGE_INT*LARGE_INT);
    return 0;
}
