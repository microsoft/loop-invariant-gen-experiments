extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop15.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop15.tmp.c"
# 32 "MAP/SAFE-exbench/TRACER-testloop15.tmp.c"
int main()
{
  int i = 0;
  int N = 100;

  while (i<N) {
    i++;
  }

  __VERIFIER_assert(!( i>N ));

  return 0;
}
