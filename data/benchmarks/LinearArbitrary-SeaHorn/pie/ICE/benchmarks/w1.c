extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

//pre: n >= 0
void main() {
	int n = __VERIFIER_nondet_int();
	if(n < 0)
	  return;

	int x = 0;

 	while (x < n) {

		x = x + 1;

	}
	__VERIFIER_assert(x == n);

}
