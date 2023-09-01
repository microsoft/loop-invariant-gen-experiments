/*
 * Benchmarks contributed by Divyesh Unadkat[1,2], Supratik Chakraborty[1], Ashutosh Gupta[1]
 * [1] Indian Institute of Technology Bombay, Mumbai
 * [2] TCS Innovation labs, Pune
 *
 */

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);

int N;

int main()
{
	N = __VERIFIER_nondet_int();
	if(N <= 0) return 1;
	__VERIFIER_assume(N <= 2147483647/sizeof(int));

	int i, j;
	int sum[1];
	int a[N];
	int b[N];

	for (i = 0; i < N; i++)
	{
		b[i] = 0;
	}

	sum[0] = 0;
	for (i = 0; i < N; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	for (i = 0; i < N; i++)
	{
		for (j = i; j < N; j++)
		{
			b[j] = b[j] + sum[0];
		}
	}

	for (i = 0; i < N; i++)
	{
		__VERIFIER_assert(b[i] == (i+1)*sum[0]);
	}

}

