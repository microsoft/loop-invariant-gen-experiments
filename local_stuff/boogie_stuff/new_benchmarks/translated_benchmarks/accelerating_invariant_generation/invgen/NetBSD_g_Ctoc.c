int main()
{
  int BASE_SZ;
  int i;
  int j;
  int len = BASE_SZ;

  if (!(BASE_SZ > 0))
  {
    return;
  }

  assert(0 <= BASE_SZ - 1);

  if (len == 0)
  {
    return;
  }

  i = 0;
  j = 0;
  while (true)
  {
    if (len == 0)
    {
      return;
    }
    else
    {
      assert(0 <= j);
      assert(j < BASE_SZ);
      assert(0 <= i);
      assert(i < BASE_SZ);
      if (unknown())
      {
        i++;
        j++;
        return;
      }
    }
    i++;
    j++;
    len--;
  }
}
