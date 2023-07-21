extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);

int N;
int main ( ) {
	N = __VERIFIER_nondet_int();
	int a[N];
	int i = 0;
	while ( i < N ) {
		a[i] = 42;
		i = i + 1;
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  a[x] == 43  );
	}
	return 0;
}
