extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
int unknown(){int x; return x;}
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop13.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop13.tmp.c"
# 24 "MAP/SAFE-exbench/TRACER-testloop13.tmp.c"

int main()
{
  int lock, old, new;
  old = __VERIFIER_nondet_uint();
  lock=0;
  new=old+1;

  while (new != old) {
    lock = 1;
    old = new;
    if (unknown()) {
      lock = 0;
      new+=2;
    }
  }

  __VERIFIER_assert(!( lock==0 ));
  return 0;
}
