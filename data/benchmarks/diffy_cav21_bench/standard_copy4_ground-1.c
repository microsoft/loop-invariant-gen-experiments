extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

/*@
	requires N > 0;
	requires \separated(a1+(0..N-1), a2+(0..N-1), a3+(0..N-1), a4+(0..N-1), a5+(0..N-1));
*/
int main(int* a1, int* a2, int* a3, int* a4, int* a5, int N ) {
	int a;
	for ( a = 0 ; a < N ; a++ ) {
		a1[a] = __VERIFIER_nondet_int();
	}

	int i;
	for ( i = 0 ; i < N ; i++ ) {
		a2[i] = a1[i];
	}
	for ( i = 0 ; i < N ; i++ ) {
		a3[i] = a2[i];
	}
	for ( i = 0 ; i < N ; i++ ) {
		a4[i] = a3[i];
	}
	for ( i = 0 ; i < N ; i++ ) {
		a5[i] = a4[i];
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  a1[x] == a5[x]  );
	}
	return 0;
}

