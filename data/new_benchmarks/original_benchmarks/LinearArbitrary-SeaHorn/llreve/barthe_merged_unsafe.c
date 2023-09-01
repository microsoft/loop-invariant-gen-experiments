extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
void main() {
	int n, c;
	int i;
	int j1, j2;
	int x1, x2;

	n = unknown();
	c = unknown();
	i = 0;
	j1 = 0; // <--- j is assigned 0
	x1 = 0;
	j2 = c; // <--- j is assigned c
	x2 = 0;

	while(/*__mark(42) &&*/ i < n) {
		j1 = 5*i + c;

		x1 = x1 + j1;
		x2 = x2 + j2;
		assert(x1==x2);

		j2 = j2 + 5;
		if (i == 10) {
		  j2 = 10;
		}
		i++;
	}
}
