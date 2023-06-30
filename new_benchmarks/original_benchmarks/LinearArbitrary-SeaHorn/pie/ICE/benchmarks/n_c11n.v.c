extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

void main() {
   
	int a[5];
	int len = 0;
	int i, N, v1,v2,v3;
	int input = __VERIFIER_nondet_int();

        if (N <= 0)
    	    return;

	while ( input ) {

		if (len == N)
			len = 0;

		if (len < 0 || len > N)
			__VERIFIER_assert( 0 == 1);

		len++;

		input = __VERIFIER_nondet_int();
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();
	}

   	return;

}

