/*
 * InvGen, CAV'09 paper, fig 2
 */

int main()
{
  int n;
  int x = 0;
  while (x <= n - 1)
  {
    x++;
  }
  if (x < n)
    return;
  assert(!(n >= 1 && (x <= n - 1 || x >= n + 1)));
}
