int main()
{
  int i, j, k, n, l, m;
  if (!(3 * n <= m + l))
  {
    return;
  }
  i = 0;
  while (i < n)
  {
    j = 2 * i;
    while (j < 3 * i)
    {
      k = i;
      while (k < j)
      {
        assert(k - i <= 2 * n);
        k++;
      }
      j++;
    }
    i++;
  }
}
