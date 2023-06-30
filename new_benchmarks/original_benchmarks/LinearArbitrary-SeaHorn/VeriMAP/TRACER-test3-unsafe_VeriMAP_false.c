extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/UNSAFE-exbench/TRACER-test3-unsafe.tmp.c"
# 1 "<command-line>"
# 1 "MAP/UNSAFE-exbench/TRACER-test3-unsafe.tmp.c"
# 22 "MAP/UNSAFE-exbench/TRACER-test3-unsafe.tmp.c"

void main(){
  int x=0;
  int y=0;

  if (unknown())
    x = 5;
  else
    y = 10;

  __VERIFIER_assert(!( x==5 || y==10 ));
  return;
}
