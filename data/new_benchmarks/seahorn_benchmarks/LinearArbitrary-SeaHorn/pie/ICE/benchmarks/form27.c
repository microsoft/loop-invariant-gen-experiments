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
  int x1,x2,x3,x4,x5;
  int x1p,x2p,x3p,x4p,x5p, input;

  x1 = x2 = x3 = x4 = x5 = 0;
  input = __VERIFIER_nondet_int();
  while(input)
  {
    x1p = __VERIFIER_nondet_int();
    x2p = __VERIFIER_nondet_int();
    x3p = __VERIFIER_nondet_int();
    x4p = __VERIFIER_nondet_int();
    x5p = __VERIFIER_nondet_int();

    if (0 <= x1p && x1p <= x4p + 1 && x2p == x3p && (x2p <= -1 || x4p <= x2p + 2) && x5p == 0)
    {
	x1 = x1p;
	x2 = x2p;
	x3 = x3p;
	x4 = x4p;
	x5 = x5p;
    }
    input = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(0 <= x1 && x1 <= x4 + 1 && x2 == x3 && (x2 <= -1 || x4 <= x2 + 2) && x5 == 0);
}

