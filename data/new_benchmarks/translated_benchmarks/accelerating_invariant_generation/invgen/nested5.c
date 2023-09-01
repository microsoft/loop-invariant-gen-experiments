int main()
{
  int i, j, k, n;
  i = 0;
  while (i < n)
  {
    j = i;
    while (j < n)
    {
      k = j;
      while (k < n)
      {
        assert(k >= i);
        k++;
      }
      j++;
    }
    i++;
  }
}
