extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testabs6.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testabs6.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testabs6.tmp.c"
//int error=0;
void main(){
  int x,y,z;

  if(z>0){
    x=4;
    y=1;
  }
  else{
    x=100;
    y=2;
  }
# 41 "MAP/SAFE-exbench/TRACER-testabs6.tmp.c"
  __VERIFIER_assert(!( x<=0 ));

}
