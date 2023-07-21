extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int SIZE;
int main( ) {
	SIZE = __VERIFIER_nondet_int();
	int a[SIZE];
	int b[SIZE];
	int i = 0;
	int c [SIZE];
	int rv[1];

	rv[0] = 1;
	for (int j = 0; j < SIZE ; j++ ) {
		a[j] = __VERIFIER_nondet_int();
		b[j] = __VERIFIER_nondet_int();
	}

	while ( i < SIZE ) {
		if ( a[i] != b[i] ) {
			rv[0] = 0;
		}
		c[i] = a[i];
		i = i+1;
	}

	int x;

	for ( x = 0 ; x < SIZE ; x++ ) {
		__VERIFIER_assert(  a[x] == c[x]  );
	}
	return 0;
}
