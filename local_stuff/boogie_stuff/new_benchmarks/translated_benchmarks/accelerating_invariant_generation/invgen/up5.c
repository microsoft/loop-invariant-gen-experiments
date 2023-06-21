int main()
{
  int n;
  int i = 0;
  int k = 0;
  while (i < n)
  {
    i++;
    k = k + 2;
  }
  int j = 0;
  while (j < n)
  {
    if (k <= 0)
    {
      assert(false);
    }
    j = j + 2;
    k--;
  }
}
