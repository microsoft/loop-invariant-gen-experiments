extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int SIZE;
int main( ) {
	SIZE = __VERIFIER_nondet_int();
	int i;
	int a[SIZE];
	int b[SIZE];
	int rv[1];

	for (i = 0; i < SIZE ; i++ ) {
		a[i] = __VERIFIER_nondet_int();
		b[i] = __VERIFIER_nondet_int();
	}

	rv[0] = 1;
	i = 0;
	while ( i < SIZE ) {
		if ( a[i] != b[i] ) {
			rv[0] = 0;
		}
		i = i+1;
	}

	int x;
	for ( x = 0 ; x < SIZE ; x++ ) {
		__VERIFIER_assert( rv[0] == 0 || a[x] == b[x]  );
	}
	return 0;
}
