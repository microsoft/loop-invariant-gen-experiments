extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n = unknown();
    int i1 = 1; // <--- i is assigned 1
    int /* predicates{} */ j1 = 0;

    int i2 = 0; // <--- i is assigned 0
    int j2 = 0;

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
