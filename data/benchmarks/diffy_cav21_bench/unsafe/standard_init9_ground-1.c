extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;
int main ( ) {
	N = __VERIFIER_nondet_int();
	int a [N];
	int i = 0;
	while ( i < N ) {
		a[i] = 42;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 43;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 44;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 45;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 46;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 47;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 48;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 49;
		i = i + 1;
	}
	i = 0;
	while ( i < N ) {
		a[i] = 50;
		i = i + 1;
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(  a[x] == 49  );
	}
	return 0;
}
