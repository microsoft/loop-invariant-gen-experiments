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
        if (unknown())
        {
          j = j + 1;
        }
      }
      if (unknown())
      {
        break;
      }
      i = j;
      j = 2 * j;
    }
    if (l > 1)
    {
      assert(l <= n);
      l--;
    }
    else
    {
      r--;
    }
  }
}
