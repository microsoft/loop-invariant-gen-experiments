int main()
{
  int n;
  int i = 0;
  int k = 0;
  while (i < n)
  {
    i = i + 2;
    k++;
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
