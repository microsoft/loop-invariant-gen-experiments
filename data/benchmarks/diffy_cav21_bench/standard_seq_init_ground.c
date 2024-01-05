extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int SIZE;
int main( ) {
	SIZE = __VERIFIER_nondet_int();
	int a[SIZE];
	int i;

	a[0] = 7;
	i = 1;
	while( i < SIZE ) {
		a[i] = a[i-1] + 1;
		i = i + 1;
	}

	int x;
	for ( x = 1 ; x < SIZE ; x++ ) {
		__VERIFIER_assert(  a[x] >= a[x-1]  );
	}
	return 0;
}
