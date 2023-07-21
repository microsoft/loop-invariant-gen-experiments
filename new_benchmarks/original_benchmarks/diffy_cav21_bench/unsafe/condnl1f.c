
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);

int N;

int main()
{
	N = __VERIFIER_nondet_int();
	if(N <= 0) return 1;

	int i;
	int sum[1];
	int a[N];
	int c[N];

	sum[0] = 0;
	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + i;
	}

	for(i=0; i<N; i++)
	{
		a[i] = N*(N+1)/2;
	}

	for(i=0; i<N; i++)
	{
		if(i != 2 && N % (i-2) == 1)
		{
			c[i] = sum[0];
		} else {
			c[i] = a[i];
		}
	}

	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(c[i] == N*(N+1)/2); 
	}
	return 1;
}
