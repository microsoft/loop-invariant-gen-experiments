int main()
{
  int i, j, k, n, m;
  if (!(m + 1 < n))
  {
    return;
  }
  i = 0;
  while (i < n)
  {
    j = i;
    while (j < m)
    {
      if (unknown())
      {
        assert(j >= 0);
        j++;
        k = 0;
        while (k < j)
        {
          assert(k < n);
          k++;
        }
      }
      else
      {
        assert(n + j + 5 > i);
        j += 2;
      }
    }
    i += 4;
  }
}
