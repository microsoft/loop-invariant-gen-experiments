/*
 * "nest-if8" from InvGen benchmark suite
 */

int main()
{
  int i, j, k, n, m;
  if (m + 1 > n - 1)
    return;
  i = 0;
  while (i <= n - 1)
  {
    j = i;
    while (j <= m - 1)
    {
      if (unknown())
      {
        assert(!(j <= -1));
        if (j < 0)
          return;
        j++;
        k = 0;
        while (k < j)
        {
          k++;
        }
      }
      else
      {
        assert(!(n + j + 5 <= i));
        if (n + j + 5 < i + 1)
          return;
        j += 2;
      }
    }
    if (j < m)
      return;
    i += 4;
  }
}
