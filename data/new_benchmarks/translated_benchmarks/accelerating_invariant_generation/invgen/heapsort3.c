int main()
{
  int n, l, r, i, j;
  assume(1 <= n);
  l = n / 2 + 1;
  r = n;
  if (l > 1)
  {
    l--;
  }
  else
  {
    r--;
  }
  while (r > 1)
  {
    i = l;
    j = 2 * l;
    while (j <= r)
    {
      if (j < r)
      {
        assert(1 <= j);
        assume(j <= n);
        assume(1 <= j + 1);
        assume(j + 1 <= n);
        if (unknown())
        {
          j = j + 1;
        }
      }
      assume(1 <= j);
      assume(j <= n);
      assume(1 <= i);
      assume(i <= n);
      assume(1 <= j);
      assume(j <= n);
      i = j;
      j = 2 * j;
    }
    if (l > 1)
    {
      assume(1 <= l);
      assume(l <= n);
      l--;
    }
    else
    {
      assume(1 <= r);
      assume(r <= n);
      r--;
    }
  }
}
