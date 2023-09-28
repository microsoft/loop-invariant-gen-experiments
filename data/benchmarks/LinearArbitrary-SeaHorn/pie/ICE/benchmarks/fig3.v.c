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

	int y = __VERIFIER_nondet_int();
	int lock, v1,v2,v3;
	lock = 0;
	int x = __VERIFIER_nondet_int();
	int input;

	// Converting do-while to a while loop by stripping the first iteration
	{
		lock = 1;
		x = y;
		input = __VERIFIER_nondet_int();
		if( input ) {

			lock = 0;
			y = y + 1;
		}
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();

	}

	while(x != y) {

		lock = 1;
		x = y;
		input = __VERIFIER_nondet_int();
		if ( input ) {

			lock = 0;
			y = y + 1;
		}
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();
	}

	__VERIFIER_assert(lock == 1);

}
//post: lock = 1
