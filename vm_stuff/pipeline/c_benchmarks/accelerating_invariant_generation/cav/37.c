/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

int main()
{
  int x = 0;
  int m = 0;
  int n = unknown_int();
  while (x <= n - 1)
  {
    if (unknown())
    {
      m = x;
    }
    x = x + 1;
  }
  if (x < n)
    return;
  assert(!(n >= 1 && (m <= -1 || m >= n)));
}
