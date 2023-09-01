// Source: E. De Angelis, F. Fioravanti, J. A. Navas, M. Proietti:
// "Verification of Programs by Combining Iterated Specialization with
// Interpolation", HCVS 2014

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

void main() {
    int x = 1;
    int y = 0;
    while (y < 1000 && __VERIFIER_nondet_int()) {
	x = x + y;
	y = y + 1;
    }
    __VERIFIER_assert(x >= y);
}
