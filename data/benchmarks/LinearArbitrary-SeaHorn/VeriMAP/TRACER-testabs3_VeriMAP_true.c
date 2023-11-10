extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testabs3.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testabs3.tmp.c"
# 28 "MAP/SAFE-exbench/TRACER-testabs3.tmp.c"
void main(){
  int sum;
  int c1, c2, c3, c4, c5;
  int d1, d2, d3, d4, d5;
  int e1, e2, e3, e4, e5;
  int f1, f2, f3, f4, f5;

  sum = 0;

  if (c1 == 0) sum=sum+1; else sum=sum+2;
  if (c2 == 0) sum=sum+1; else sum=sum+2;
  if (c3 == 0) sum=sum+1; else sum=sum+2;
  if (c4 == 0) sum=sum+1; else sum=sum+2;
  if (c5 == 0) sum=sum+1; else sum=sum+2;

  if (d1 == 0) sum=sum+1; else sum=sum+2;
  if (d2 == 0) sum=sum+1; else sum=sum+2;
  if (d3 == 0) sum=sum+1; else sum=sum+2;
  if (d4 == 0) sum=sum+1; else sum=sum+2;
  if (d5 == 0) sum=sum+1; else sum=sum+2;

  if (e1 == 0) sum=sum+1; else sum=sum+2;
  if (e2 == 0) sum=sum+1; else sum=sum+2;
  if (e3 == 0) sum=sum+1; else sum=sum+2;
  if (e4 == 0) sum=sum+1; else sum=sum+2;
  if (e5 == 0) sum=sum+1; else sum=sum+2;

  if (f1 == 0) sum=sum+1; else sum=sum+2;
  if (f2 == 0) sum=sum+1; else sum=sum+2;
  if (f3 == 0) sum=sum+1; else sum=sum+2;
  if (f4 == 0) sum=sum+1; else sum=sum+2;
  if (f5 == 0) sum=sum+1; else sum=sum+2;

  __VERIFIER_assert(!( sum > 40 ));

  return;
}
