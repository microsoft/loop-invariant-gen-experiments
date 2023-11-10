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
  int x1,x2,x3;
  int x1p,x2p,x3p, input;

  x1 = x2 = x3 = 0;
  input = __VERIFIER_nondet_int();
  while(input)
  {
    x1p = __VERIFIER_nondet_int();
    x2p = __VERIFIER_nondet_int();
    x3p = __VERIFIER_nondet_int();

    if (x1p <= x2p && (x2p >= 0 || x2p - x3p <= 2))
    {
	x1 = x1p;
	x2 = x2p;
	x3 = x3p;
    }
    input = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(x1 <= x2 && (x2 >= 0 || x2 - x3 <= 2));    
}

