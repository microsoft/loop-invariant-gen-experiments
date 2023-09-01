extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
int __mark(int);
void main() {
	int x = unknown();
    int i1 = 0; // <--- i iterates from 0 to 10
	int i2 = 10; // <--- i iterates from 10 to 0

    while (/*__mark(42) &*/ (i1 <= 10)) {
        //__mark(42);
        if (i1 == x) {
            break;
        }
        i1++;
    }

    while (/*__mark(42) &*/ (i2 >= 0)) {
        //__mark(42);
        if (i2 == (10 - x)) {
            break;
        }
        i2--;
    }

	assert(i1==10-i2);
}
