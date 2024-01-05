extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n = unknown();
    int x1 = 0;
    int x2 = 0;

    int i1 = 0; // <--- i is assigned 0
    int i2 = 1; // <--- i is assigned 1
	while (1)
	{
    	if (/*__mark(2) &&*/ i1 <= n) {
	        x1 = x1 + i1;
    	    i1++;
	    }

		if (/*__mark(2) &&*/ i2 <= n) {
	        x2 = x2 + i2;
    	    i2++;
		}

		if (i1>n && i2>n) break;
		assert(x2==x1+i1);
    }
}
