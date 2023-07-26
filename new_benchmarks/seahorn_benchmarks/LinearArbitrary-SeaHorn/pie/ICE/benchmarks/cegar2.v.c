extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

//pre: true
int main() {

	int N = __VERIFIER_nondet_int();
	int x = 0;
	int m = 0;
	int input, v1, v2, v3;

 	while (x < N) {

		input = __VERIFIER_nondet_int();
		if( input ) {

			m = x;
		}

		x = x + 1;
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();

	}

	if (N > 0) {
		__VERIFIER_assert((0 <= m) && (m < N));
	}

}
