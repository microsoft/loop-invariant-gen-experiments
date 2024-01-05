extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();


/*@
	requires N > 0;
	requires \separated(a1+(0..N-1), a2+(0..N-1));
*/
int main(int* a1, int* a2, int N) {
	int a;
	for ( a = 0 ; a < N ; a++ ) {
		a1[a] = __VERIFIER_nondet_int();
	}

	int i;
	for ( i = 0 ; i < N ; i++ ) {
		a2[i] = a1[i];
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  a1[x] == a2[x]  );
	}
	return 0;
}

