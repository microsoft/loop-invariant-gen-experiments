extern void __VERIFIER_error() __attribute__ ((__noreturn__));
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
extern int __VERIFIER_nondet_int();

int N;
int main ( ) {
	N = __VERIFIER_nondet_int();
	int a[N];
	int b[N]; 
	int i;
	int f[1];

	for(i = 0; i< N; i++) 
	{ 
		a[i] = __VERIFIER_nondet_int();
	}

	for(i = 0; i< N; i++) 
	{ 
		if ( a[i] >= 0 ) b[i] = 1;
		else b[i] = 0;
	}

	f[0] = 1;
	for(i = 0; i< N; i++) 
	{ 
		if ( a[i] >= 0 && !b[i] ) f[0] = 0;
		if ( a[i] < 0 && !b[i] ) f[0] = 0;
	}

	__VERIFIER_assert ( f[0] == 1 ); 
	return 0;
}
