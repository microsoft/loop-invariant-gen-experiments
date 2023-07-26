extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

void foo(int i, int j) {

	int x = i;
	int y = j;
	int v1,v2,v3;

 	while (x != 0) {
		x--;
		y--;
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();
	}

	if (i == j)
		__VERIFIER_assert(y == 0);

}

int main()
{
  int i = __VERIFIER_nondet_int(), j = __VERIFIER_nondet_int();
  foo(i, j);
}
