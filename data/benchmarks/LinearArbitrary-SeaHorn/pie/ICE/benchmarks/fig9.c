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

	int x, y;
	x = 0;
	y = 0;

	while(y >= 0) {

		y = y + x;
	
	}

	__VERIFIER_assert(0 == 1);

}
