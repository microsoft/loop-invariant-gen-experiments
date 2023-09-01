int main()
{
  int n;
  int k = 0;
  int i = 0;
  while (i < n)
  {
    i++;
    k++;
  }
  int j = n;
  while (j > 0)
  {
    assert(k > 0);
    j--;
    k--;
  }
}
