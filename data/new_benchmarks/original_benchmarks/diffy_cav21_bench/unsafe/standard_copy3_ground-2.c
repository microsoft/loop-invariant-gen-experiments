extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;

int main( ) {
	N = __VERIFIER_nondet_int();
	int a1[N];
	int a2[N];
	int a3[N];
	int a4[N];

	int a;
	for ( a = 0 ; a < N ; a++ ) {
		a1[a] = __VERIFIER_nondet_int();
		a3[a] = __VERIFIER_nondet_int();
	}

	int i;
	for ( i = 0 ; i < N ; i++ ) {
		a2[i] = a1[i];
	}
	for ( i = 0 ; i < N ; i++ ) {
		a4[i] = a2[i];
	}
	for ( i = 0 ; i < N ; i++ ) {
		a4[i] = a3[i];
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  a1[x] == a4[x]  );
	}
	return 0;
}

