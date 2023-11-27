extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

/*@
	requires SIZE > 0;
	requires \separated(a+(0..SIZE-1), b+(0..SIZE-1));
*/
int main(int* a, int* b, int SIZE)
{
	int i;
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
