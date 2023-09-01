extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop16.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop16.tmp.c"
# 22 "MAP/SAFE-exbench/TRACER-testloop16.tmp.c"
void main(int N)
{
  int i, x;

  x = 1;
  i = 0;

  while (i<N) {
    if (x==1) {
      x=2;
    } else {
      x=1;
    }
    i++;
  }

  __VERIFIER_assert(!( x>2 ));

  return;
}
