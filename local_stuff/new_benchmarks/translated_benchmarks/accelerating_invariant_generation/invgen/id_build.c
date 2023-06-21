int main()
{
  int offset, length, nlen;
  int i, j;
  i = 0;
  while (i < nlen)
  {
    j = 0;
    while (j < 8)
    {
      assert(0 <= nlen - 1 - i);
      assert(nlen - 1 - i < nlen);
      j++;
    }
    i++;
  }
}
