int main()
{
  int i, j, k, n, m;
  if (!(n <= m))
  {
    return;
  }
  i=0;
  while(i < n){
    j=0;
    while(j < n)
    {
      k = j;
      while (k < n + m)
      {
        assert(i + j <= n + k + m);
        k++;
      }
      j++;
    }
    i++;
  }
}
