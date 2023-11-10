extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop7.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop7.tmp.c"
# 26 "MAP/SAFE-exbench/TRACER-testloop7.tmp.c"
//int unknown(){int x; return x;}

void main()
{
  int x, y;

  y = 0;
  x = 1;
  while ( unknown() < 10) {
    if (x<2) {
      x=2;
    } else {
      x=1;
    }
    if (y<1) {
      y=0;
    }
  }
  __VERIFIER_assert(!( x > 2 ));
  return;
}
