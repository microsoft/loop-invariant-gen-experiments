extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp17.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp17.tmp.c"
# 19 "MAP/SAFE-exbench/TRACER-testwp17.tmp.c"
main(){
  int x;
  int NONDET;

  if(NONDET>0)


    x=0;
  else
    x=1;
# 37 "MAP/SAFE-exbench/TRACER-testwp17.tmp.c"
  if (x==0){


    __VERIFIER_assert(!( x !=0 ));
  }
}
