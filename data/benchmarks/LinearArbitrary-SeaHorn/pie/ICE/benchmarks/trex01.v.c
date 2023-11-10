extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}


void foo(int d) {
  int x, y, k, z = 1;
  int v1, v2, v3;
  int c;
  int input;
  L1:
  while (z < k) {
    z = 2 * z; 
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(z>=1);

  L2:
  while (x > 0 && y > 0) {
    c = __VERIFIER_nondet_int();
    if (c) {
      P1:
      x = x - d;
      y = __VERIFIER_nondet_int();
      z = z - 1;
    } else {
      y = y - d;
    }
  }
}

int main()
{
  int d;
  foo(d);
}
