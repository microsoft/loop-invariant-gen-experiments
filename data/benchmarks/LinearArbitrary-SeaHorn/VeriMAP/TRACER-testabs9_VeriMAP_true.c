extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testabs9.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testabs9.tmp.c"
# 27 "MAP/SAFE-exbench/TRACER-testabs9.tmp.c"
void main(){

  int x,y;
  y=99;
  x=0;

  __VERIFIER_assert(!( x<0 ));
}
