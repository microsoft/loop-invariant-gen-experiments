extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;
int main( ) {
	N = __VERIFIER_nondet_int();
	int i; 
	int a[N];
	int b[N];
	int c[1];

	for(i = 0; i < N; i++) 
	{
		a[i] = __VERIFIER_nondet_int();
		b[i] = __VERIFIER_nondet_int();
	}

	c[0] = 0;
	i = 0;
	while ( i < N ) {
		if( a[i] != b[i] ) c[0] = 1;
		i = i + 1;
	}

	int x;
	for ( x = 0 ; x < N ; x++ ) {
		__VERIFIER_assert(c[0] == 1 ||  a[x] == b[x]  );
	}
	return 0;
}
