int main()
{
  int i, k, n;
  k = 1;
  while (k < n)
  {
    i = 1;
    while (i < n)
    {
      assert(1 <= k);
      i++;
    }
    if (i < n)
    {
      i = 1;
      while (i < n)
      {
        i++;
      }
    }
    k++;
  }
}
