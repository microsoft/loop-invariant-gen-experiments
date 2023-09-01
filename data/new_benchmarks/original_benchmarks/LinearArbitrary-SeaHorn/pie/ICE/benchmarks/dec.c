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
  int x, m;
  x = 100;
  while(x > 0)
  {
    m = __VERIFIER_nondet_int();
    x = x - 1;
  }
  __VERIFIER_assert(x == 0);    
}

