extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp9.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp9.tmp.c"
# 18 "MAP/SAFE-exbench/TRACER-testwp9.tmp.c"
void main(){
  int x = __VERIFIER_nondet_uint();


  if (x>10){
    __VERIFIER_assert(!( x < 5 ));
    x=x+2;
  }

}
