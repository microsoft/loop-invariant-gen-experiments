extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

main()
{
  int x, N, v1,v2,v3;
  x = 0;
  N = __VERIFIER_nondet_int();
  while(x < N)
  {
    x = x + 1;
    v1 = __VERIFIER_nondet_int();
    v2 = __VERIFIER_nondet_int();
    v3 = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(N < 0 || x == N);    
}

