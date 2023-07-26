extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
/*
 * Two computations for a Fibonacci number.
 * The left starts with (0, 1, 1, ...) while the right starts with
 * (1, 1, 2, ...). They are not equivalent.
 *
 * However, if they are not started with the same input (n1 == n2) but
 * with n1 == n2 + 1, results are equal.
 * This can be expressed using a "rel_in" specification.
 */
void main() {
	int n = unknown();
  int f1 = 0;   //  <---- starting at 0
  int f2 = 1;  //  <---- starting at 1
  int g1 = 1, g2 = 1;
  int h1 = 0, h2 = 0;

  while((n > 0)) {
    h1 = f1 + g1;
    f1 = g1;
    g1 = h1;
    n --;

    h2 = f2 + g2;
    f2 = g2;
    g2 = h2;

	assert(h2==h1+f1);
  }
}
