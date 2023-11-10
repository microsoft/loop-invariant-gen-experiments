extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop4.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop4.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testloop4.tmp.c"
void main(){
  int x,N;
  int a;

  a=0;
  N =10;
  x = 0;
  do {
    x=x+1;
  } while (x != N);

  __VERIFIER_assert(!( a > 1 ));
}
