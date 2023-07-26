extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp13.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp13.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testwp13.tmp.c"
main(){

  int x,y;
  x = __VERIFIER_nondet_uint();
  y = __VERIFIER_nondet_uint();

  if (x>5){
    if (y>0)
      y++;
    else
      x=x-10;

    if (x<50){
      __VERIFIER_assert(!( x < 0 ));
    }
  }
}
