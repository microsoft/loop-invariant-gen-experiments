int main()
{
  int i, pvlen;
  int tmp___1;
  int k = 0;
  int n;

  i = 0;

  while (unknown())
  {
    i = i + 1;
  }
  if (i > pvlen)
  {
    pvlen = i;
  }
  i = 0;

  while (unknown())
  {
    tmp___1 = i;
    i = i + 1;
    k = k + 1;
  }

  int j = 0;
  n = i;
  while (true)
  {
    assert(k >= 0);
    k = k - 1;
    i = i - 1;
    j = j + 1;
    if (!(j < n))
    {
      break;
    }
  }
  return;
}
