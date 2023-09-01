extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

int main() {
   
	int a[5];
	int len = 0;
	int i;
	int input = __VERIFIER_nondet_int();

	while ( input ) {

		if (len == 4)
			len = 0;

		if (len < 0 || len >= 5)
			__VERIFIER_assert( 0 == 1);

		len++;

		input = __VERIFIER_nondet_int();
	}

   	return 1;

}

