int main()
{
  int i, k, n, l;
  assume(l > 0);
  k = 1;
  while (k < n)
  {
    i = l;
    while (i < n)
    {
      i++;
    }
    i = l;
    while (i < n)
    {
      assert(1 <= i);
      i++;
    }
    k++;
  }
}