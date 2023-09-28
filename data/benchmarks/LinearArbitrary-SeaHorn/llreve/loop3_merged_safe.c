extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n = unknown();
    int i1 = 1;
    int j1 = 0; // <--- j is assigned 0
    int i2 = 1;
    int j2 = 2; // <--- j is assigned 2

    if (n < 1) {
        n = 1;
    }

    while (i1 <= n) {
        j1 = j1 + 2;
		assert(j1==2*i1);
        i1++;
    }

    while (i2 < n) {
        j2 = j2 + 2;
        i2++;
		assert(j2==2*i2);
    }

	assert(j1==j2);
}
