extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testwp16.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testwp16.tmp.c"
# 21 "MAP/SAFE-exbench/TRACER-testwp16.tmp.c"
main(){

  int t,x2,x3,temp;


  t = 1;
  x2 = temp;
  x3 = temp;



  if (x2 == 0){

    if (x3 == 3)
      t++;
  }


  t++;

  __VERIFIER_assert(!(t>1000));

}
