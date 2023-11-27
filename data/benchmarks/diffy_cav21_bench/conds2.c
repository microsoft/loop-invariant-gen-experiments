
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);


/*@
requires N > 0;
requires \separated(a+(0..N-1), c+(0..N-1));
*/
int main(int* a, int* c, int N)
{

	int i;
	int sum[1];

	sum[0] = 0;
	for(i=0; i<N; i++)
	{
		a[i] = 1;
	}

	for(i=0; i<N; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	for(i=0; i<N; i++)
	{
		if(sum[0] == N + 1)
		{
			c[i] = sum[0];
		} else {
			c[i] = sum[0] + a[i];
		}
	}

	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(c[i] == N+1);
	}
	return 1;
}
