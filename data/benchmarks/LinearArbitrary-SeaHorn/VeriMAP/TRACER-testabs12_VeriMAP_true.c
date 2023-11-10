void __VERIFIER_assume(int cond) {if (!cond) {LOOP: goto LOOP;}};
extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testabs12.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testabs12.tmp.c"
# 18 "MAP/SAFE-exbench/TRACER-testabs12.tmp.c"
main(){
  int i,count,n;
  count = __VERIFIER_nondet_uint();
  __VERIFIER_assume( count >= 0 );
  i=0;


  while (i < 100 ){
      count++;
      i++;
  }

  __VERIFIER_assert(!( (i > 100 ) || count < 0 ));
}
