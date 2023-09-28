extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop29.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop29.tmp.c"
# 22 "MAP/SAFE-exbench/TRACER-testloop29.tmp.c"
main() {
  int x = 0;
  while(x < 100) {
    x++;
    if(x == 50)
      break;
  }
  __VERIFIER_assert(!( x != 50 ));
}
