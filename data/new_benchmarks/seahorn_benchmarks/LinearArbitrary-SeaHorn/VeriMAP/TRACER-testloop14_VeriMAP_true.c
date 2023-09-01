extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop14.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop14.tmp.c"
# 27 "MAP/SAFE-exbench/TRACER-testloop14.tmp.c"
int main()
{
  int i, x, y;
  x = __VERIFIER_nondet_uint();
  y = __VERIFIER_nondet_uint();
  if (y <= 2) {
    if (x < 0) {
      x = 0;
    }
    i = 0;
    while (i < 10) {
      __VERIFIER_assert(!( y > 2 ));
      i++;
    }

    __VERIFIER_assert(!( x <= -1 ));
  }
  return 0;
}
