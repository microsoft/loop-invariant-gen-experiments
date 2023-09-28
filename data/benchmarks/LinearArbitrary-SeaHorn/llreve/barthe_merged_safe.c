extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
extern int __mark(int);
void main() {
	int n, c;
    n = unknown();
    c = unknown();
    int i = 0;
    int j1 = 0;
    int x1 = 0;
    int j2 = c;
    int x2 = 0;

    while (/*__mark(42) &&*/ (i < n)) {
        /* __mark(42); */
        j1 = 5 * i + c;
		assert(j1 == j2);

        x1 = x1 + j1;
        x2 = x2 + j2;
		assert(x1 == x2);

        j2 = j2 + 5;
        i++;
    }
}
