extern void __VERIFIER_error() __attribute__((noreturn));
void assert (int cond) { if (!cond) __VERIFIER_error (); }
/* This example may not finish within the timeout ... */
/* Please switch off full invariants (options to the right)
 * to make this example working. 
 */
void main() {
  int n = unknown();
  int i1 = 0, i2 = 0;
  int j1 = 0, j2 = 0;

  while (1) {
    if (i1 < n + n) {
      j1++;
      i1++;
    }

    if (i2 < n) {
      j2 = j2 + 2;
      i2++;
    }
  }
  assert(j1==j2);
}
