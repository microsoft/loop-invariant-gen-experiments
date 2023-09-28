extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
# 1 "MAP/UNSAFE-exbench/TRACER-test1-unsafe.tmp.c"
# 1 "<command-line>"
# 1 "MAP/UNSAFE-exbench/TRACER-test1-unsafe.tmp.c"
# 20 "MAP/UNSAFE-exbench/TRACER-test1-unsafe.tmp.c"
int main(){
  int x = 0;

  if (unknown()) x = x+1;
  __VERIFIER_assert(!( x > 1 ));

  if (unknown()) x = x+2;
  __VERIFIER_assert(!( x > 3 ));

  if (unknown()) x = x+4;
  __VERIFIER_assert(!( x >= 7 ));
  return x;
}
