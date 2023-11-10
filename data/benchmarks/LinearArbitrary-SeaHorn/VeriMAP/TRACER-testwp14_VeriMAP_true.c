void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp14.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp14.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testwp14.tmp.c"
main(){

  int x,y,z;

  if (x>4)
    z=4;
  else
    x=5;

  __VERIFIER_assume( x>0 );

  y=x;

  __VERIFIER_assert(!( !(y > 4) ));

}
