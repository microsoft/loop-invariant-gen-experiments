extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testfunc11.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testfunc11.tmp.c"
# 23 "MAP/SAFE-exbench/TRACER-testfunc11.tmp.c"
int bar(){ return 1;}
int foo(){ return bar();}

main(){
  int x;
  x = foo();
  __VERIFIER_assert(!( x !=1 ));
}
