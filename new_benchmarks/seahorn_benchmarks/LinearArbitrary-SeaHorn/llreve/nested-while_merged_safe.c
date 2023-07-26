extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int /*@ predicates{x1<=0,x2<=0,x<=0} @*/ x0 = unknown();
    int x1=x0,x2=x0;
	int g0 = unknown();
    int g1=g0, /*@ predicates{g1==g0,g2==g0} @*/ g2=g0;
    int /*@ predicates{i1+g1==g0} @*/ i1 = 0, /*@ predicates{i2+g2==g0} @*/ i2 = 0;

    while (i1 < x1) {
        i1 = i1 + 1;
        g1 = g1 - 2; // <--- small syntactic differences
        g1 = g1 + 1;

		assert(x1>=i1);
        while (x1 < i1) {
            x1 = x1 + 2;
            x1 = x1 - 1;
            g1 = g1 + 1;
        }
    }

	assert((x0<=0 && g1==g0) || (x0>0 && g1==g0-x0));

    while (i2 < x2) {
        i2 = i2 + 1;
        g2 = g2 - 1;
        while (x2 < i2) {
            x2 = x2 + 1;
            g2 = g2 + 1;
        }
    }

	assert((x0<=0 && g2==g0) || (x0>0 && g2==g0-x0));
	assert(x1==x2);
//	assert(g1==g2);
}
