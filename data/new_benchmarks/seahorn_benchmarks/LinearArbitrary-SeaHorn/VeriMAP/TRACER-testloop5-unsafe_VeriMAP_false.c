extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testloop5.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testloop5.tmp.c"
# 20 "MAP/SAFE-exbench/TRACER-testloop5.tmp.c"

int foo(int i)
{
  i++;
  return i;
}

void main() {
  int i = 0;
  while(foo(i) < 10){}

  __VERIFIER_assert(!( i == 10 ));

}
