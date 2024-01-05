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

/*@
	requires N > 0;
	requires \separated(a+(0..N-1), b+(0..N-1));
*/
int main(int* a, int* b, int N)
{

	int i, j;
	int sum[1];

	for (i = 0; i < N; i++)
	{
		b[i] = 0;
	}

	sum[0] = 0;
	for (i = 0; i < N; i++)
	{
		for (j = 0; j < N; j++)
		{
			sum[0] = sum[0] + a[i];
		}
	}

	for (i = 0; i < N; i++)
	{
		for (j = 0; j < i+1; j++)
		{
			b[j] = b[j] + sum[0];
		}
	}

	for (i = 0; i < N; i++)
	{
		__VERIFIER_assert(b[i] == (N-i) * sum[0]);
	}
}
