extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop11.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop11.tmp.c"
# 18 "MAP/SAFE-exbench/TRACER-testloop11.tmp.c"


void main()
{
  int e, s;

  e=0;
  s=2;
  while (unknown()) {
    if (s == 2){
      if (e ==0) e=1;
      s = 3;
    }
    else if (s == 3){
      if (e ==1) e=2;
      s=4;
    }
    else if (s == 4){
      __VERIFIER_assert(!( e == 3 ));
      s=5;
    }
  }
  return;
}
