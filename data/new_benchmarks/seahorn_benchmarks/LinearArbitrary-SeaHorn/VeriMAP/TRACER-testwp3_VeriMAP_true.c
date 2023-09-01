extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp3.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp3.tmp.c"
# 21 "MAP/SAFE-exbench/TRACER-testwp3.tmp.c"
void main(){
  int x,y;
  if (y>0)
    x=2;
  else{
    x=47;
  }
  x++;
  x=x+2;
  __VERIFIER_assert(!( x > 50 ));
}
