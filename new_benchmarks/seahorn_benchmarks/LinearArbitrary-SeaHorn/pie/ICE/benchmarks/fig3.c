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
	int lock;
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
	}

	while(x != y) {

		lock = 1;
		x = y;
		input = __VERIFIER_nondet_int();
		if ( input ) {

			lock = 0;
			y = y + 1;
		}
	}

	__VERIFIER_assert(lock == 1);

}
//post: lock = 1
