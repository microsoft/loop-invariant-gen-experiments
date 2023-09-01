int main()
{
  int i, j, k, n;
  if (!(k == n))
  {
    return;
  }

  i = 0;
  while (i < n)
  {
    j = 2 * i;
    while (j < n)
    {
      if (unknown())
      {
        k = j;
        while (k < n)
        {
          assert(k >= 2 * i);
          k++;
        }
      }
      else
      {
        assert(k >= n);
        assert(k <= n);
      }
      j++;
    }
    i++;
  }
}
