extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume(int);
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int(void);

int SIZE;

int main()
{
	SIZE = __VERIFIER_nondet_int();
	if(SIZE <= 0) return 1; 

	int i;
	int a[SIZE];
	int sum[1];

	sum[0]=SIZE;
	for(i = 0; i < SIZE; i++)
	{
		a[i] = 1;
	}

	for(i = 0; i < SIZE; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	for(i = 0; i < SIZE; i++)
	{
		sum[0] = sum[0] + a[i];
	}

	for(i = 0; i < SIZE; i++)
	{
		sum[0] = sum[0] - a[i];
	}

	for(i = 0; i < SIZE; i++)
	{
		sum[0] = sum[0] - a[i];
	}

	__VERIFIER_assert(sum[0] == 0);

	return 1;
}
