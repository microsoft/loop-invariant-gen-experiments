int main()
{
  int i, n, t, k;
  int l, r, u, j;
  int x, y, z;
  x = 1;
  while (x < n)
  {
    z = 1;
    while (z + x <= n)
    {
      y = z + x * 2;
      if (y > n)
      {
        y = n + 1;
      }
      l = z;
      r = z + x;
      u = y;
      i = l;
      j = r;
      k = l;
      while (i < r && j < u)
      {
        if (unknown())
        {
          i++;
        }
        else
        {
          j++;
        }
        k++;
      }
      assert(k <= n);

      while (i < r)
      {
        i++;
        k++;
      }
      while (j < u)
      {
        j++;
        k++;
      }
      z = z + x * 2;
    }
    x = x * 2;
  }
}