extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-test1.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-test1.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-test1.tmp.c"
void main(){
  int x = 0;

  if (unknown()) x = x+1;
  if (unknown()) x = x+2;
  if (unknown()) x = x+4;

  __VERIFIER_assert(!( x > 7 ));
  return;
}
