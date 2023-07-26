extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

void main()
{
  int x, N;
  x = 0;
  N = __VERIFIER_nondet_int();
  if (N < 0)
    return;

  while(x < N)
  {
    x = x + 1;
  }
  __VERIFIER_assert(x == N);    
  return;
}

