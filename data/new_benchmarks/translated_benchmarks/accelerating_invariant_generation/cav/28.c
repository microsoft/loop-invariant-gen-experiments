/*
 * From CAV'12 by Sharma et al.
 */

int main()
{
  int x = 0;
  int y = 0;
  int n = 0;
  while (unknown())
  {
    x++;
    y++;
  }
  while (x <= n - 1 || x >= n + 1)
  {
    x--;
    y--;
  }
  if (x != n)
    return;
  assert(!(y != n));
}
