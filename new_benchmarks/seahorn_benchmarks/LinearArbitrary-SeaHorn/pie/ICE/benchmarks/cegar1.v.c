extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();;
  }
  return;
}

//pre: 0 <= x <= 2; 0 <= y <= 2
void cegar1(int x, int y) {

	int input, v1, v2, v3;
	if (!(0 <= x))
		return;
	if (!(x <= 2))
		return;
	if (!(0 <= y))
		return;
	if (!(y <= 2))
		return;

	input = __VERIFIER_nondet_int();
 	while ( input) {

		x = x + 2;
		y = y + 2;

		input = __VERIFIER_nondet_int();
		v1 = __VERIFIER_nondet_int();
		v2 = __VERIFIER_nondet_int();
		v3 = __VERIFIER_nondet_int();
	}
	__VERIFIER_assert(!((x == 4) && (y == 0)));

}
int main()
{
  int x,y;
  cegar1(x, y);
}
