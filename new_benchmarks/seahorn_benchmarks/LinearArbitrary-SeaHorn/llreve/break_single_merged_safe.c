extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
extern int __mark(int);
void main() {
	int x = unknown();
    int i1 = 0;
    while (/*__mark(42) &&*/ (i1 <= 10)) {
        /* __mark(42); */
        if (i1 == x) {
            break; // <--- conditional break
        }
        i1++;
    }

    int i2 = 0;
    while (/*__mark(42) &&*/ ((i2 <= 10) && (i2 != x))) {
        /* __mark(42); */
        i2++;
    }
	assert(i1 == i2);
}
