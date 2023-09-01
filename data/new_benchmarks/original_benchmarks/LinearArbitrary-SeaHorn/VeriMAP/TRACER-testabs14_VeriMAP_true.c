extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testabs14.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testabs14.tmp.c"
# 27 "MAP/SAFE-exbench/TRACER-testabs14.tmp.c"
main(int n){
  int i,j;

  i=0; j=0; n=10;

  while(j < n){
    j++;
  }
  while (i < n){
    i++;
  }

  __VERIFIER_assert(!( i>10 || j>10 ));

}
