extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp6.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp6.tmp.c"
# 21 "MAP/SAFE-exbench/TRACER-testwp6.tmp.c"
void main(){
  int x,y;

  if (y>0)
    x=1;
  else
    x=47;

  if (x>0)
    x=x+3;
  else
    x=x+5;

  __VERIFIER_assert(!( x > 50 ));

}
