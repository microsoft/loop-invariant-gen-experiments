extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop8.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop8.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testloop8.tmp.c"

void main () {
  int x, y;

  x = 0;
  y = 0;
  while (unknown()) {
    x ++ ;
    y ++ ;
  }
  while (x > 0) {
    x -- ;
    y -- ;
  }
  __VERIFIER_assert(!( y == 0 ));
}
