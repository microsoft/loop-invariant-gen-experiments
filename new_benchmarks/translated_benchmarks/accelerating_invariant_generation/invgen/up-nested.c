int main()
{
  int n, j, i, k;
  i = 0;
  k = 0;

  assume(j <= n);
  while (j <= n)
  {
    assume(i >= 0);
    j++;
  }
  assert(i >= 0);
}
