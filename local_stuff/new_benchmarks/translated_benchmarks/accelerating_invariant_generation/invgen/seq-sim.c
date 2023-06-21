
int main()
{
  int n, m;
  int i = 0;
  int k = 0;

  while (i < n)
  {
    i++;
    k++;
  }
  i = 0;
  while (i < m)
  {
    i++;
    k++;
  }
  i = 0;
  while (i < m)
  {
    i++;
    k--;
  }
  i = 0;
  while (i < n)
  {
    assert(k > 0);
    i++;
    k--;
  }
}
