extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);

int N;

int main( ) {
	N = __VERIFIER_nondet_int();
	int a[N];
	int min[1];

	min[0] = 0;  
	for(int j = 0; j < N; j++)
	{
		a[j] = __VERIFIER_nondet_int();
	}

	int i = 0;

	while ( i < N )
	{
		if ( a[i] < min[0] ) {
			min[0] = a[i];
		}
		i = i + 1;
	}

	int x;
	for ( x = 0 ; x < N ; x++ )
	{
		__VERIFIER_assert(a[x] > min[0]);
	}
	return 0;
}
