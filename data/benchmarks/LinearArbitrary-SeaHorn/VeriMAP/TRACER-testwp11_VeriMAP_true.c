extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp11.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp11.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testwp11.tmp.c"
main(){
  int x,y,z;
  int NONDET1,NONDET2,NONDET3;

  if (NONDET2>0)
    y=2;
  else
    y=3;

  if (NONDET3>0)
    x=4;
  else
    x=5;

  if (NONDET1>0)
    z=5;
  else
    z=6;


  __VERIFIER_assert(!( x > 10 || y > 5 ));

}
