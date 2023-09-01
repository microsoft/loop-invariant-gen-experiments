extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;

int main ( ) {
	N = __VERIFIER_nondet_int();
	int a [N];
	int b [N]; 
	int i = 0;
	while ( i < N ) {
		a[i] = 42;
		i = i + 1;
	}

	for ( i = 0 ; i < N ; i++ ) {
		b[i] = a[i];
	}

	for ( i = 0 ; i < N ; i++ ) {
		b[i] = b[i] + i;
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  b[x] == 42 + x  );
	}
	return 0;
}
