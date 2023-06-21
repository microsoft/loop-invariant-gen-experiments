int main()
{
  int n, i, k;
  assume(n >= 0);
  k = n;
  i = 0;
  while (i < n)
  {
    k--;
    i = i + 2;
  }

  int j = 0;

  while (j < n / 2)
  {
    assert(k > 0);
    k--;
    j++;
  }
}
