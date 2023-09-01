
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
	int sum1[1];
	int sum2[1];
	int c[N];

	sum1[0] = 0;
	for(i=0; i<N; i++)
	{
		sum1[0] = sum1[0] + 2;
	}

	sum2[0] = N;
	for(i=0; i<N; i++)
	{
		sum2[0] = sum2[0] + 1;
	}

	for(i=0; i<N; i++)
	{
		if(i != 0 && N % i == 0)
		{
			c[i] = sum2[0];
		} else {
			c[i] = sum1[0]; 
		}
	}

	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(c[i] == 2*N); 
	}
	return 1;
}
