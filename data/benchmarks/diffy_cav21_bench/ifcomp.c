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
	requires \separated(a+(0..N-1), b+(0..N-1), c+(0..N-1));
*/
int main(int* a, int* b, int* c, int N)
{

	int i;

	for(i=0; i<N; i++)
	{
		if(i==0) {
			a[0] = 6;
		} else {
			a[i] = a[i-1] + 6;
		}
	}

	for(i=0; i<N; i++)
	{
		if(i==0) {
			b[0] = 1;
		} else {
			b[i] = b[i-1] + a[i-1];
		}
	}

	for(i=0; i<N; i++)
	{
		if(i==0) {
			c[0] = 0;
		} else {
			c[i] = c[i-1] + b[i-1];
		}
	}

	for(i=0; i<N; i++)
	{
		__VERIFIER_assert(c[i] == i*i*i);
	}
	return 1;
}
