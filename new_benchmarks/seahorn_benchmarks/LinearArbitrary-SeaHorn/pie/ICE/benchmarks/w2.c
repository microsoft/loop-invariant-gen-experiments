extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

void main() {

	int n = __VERIFIER_nondet_int();
	if (n <= 0)
		return;

	int x = 0;
	int input = __VERIFIER_nondet_int();

 	while ( 0 == 0 ) {
		if ( input ) {

			x = x + 1;
			if (x >= n ) {
				break;
			}
		}
		input = __VERIFIER_nondet_int();
	}
	__VERIFIER_assert(x == n);

}
