int main()
{
  int i;
  int sn = 0;
  i = 1;
  while (i <= 8)
  {
    if (i < 4)
      sn = sn + 2;
    i++;
  }
  assert(sn == 8 * 2 || sn == 0);
}
