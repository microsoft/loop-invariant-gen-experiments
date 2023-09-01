extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp12.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp12.tmp.c"
# 23 "MAP/SAFE-exbench/TRACER-testwp12.tmp.c"
void main(){
  int y1,y2,y3;
  int x = 0;
  int p,z;



  if (y2>0) x=x+2;
  else y2=3;
  if (p>0) z=3;
  else z=2;
  if (y3>0) x=x+4;
  else y3=3;

  __VERIFIER_assert(!( x>6 && ( y2<0 || y3<0 ) ));
  return;
}
