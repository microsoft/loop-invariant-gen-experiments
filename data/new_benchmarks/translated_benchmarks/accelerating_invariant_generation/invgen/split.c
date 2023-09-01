int main()
{
  int k = 100;
  bool b;
  int i;
  int j;
  int n;
  i = j;
  n = 0;
  while (n < 2 * k)
  {
    if (b)
    {
      i++;
    }
    else
    {
      j++;
    }
    b = !b;
    n++;
  }
  assert(i == j);
}
