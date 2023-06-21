int main()
{
  int i;
  int j = 10;
  int n = unknown_int();
  assume(n >= 0);
  int sn = 0;
  i = 1;
  while(i <= n)
  {
    if (i < j)
      sn = sn + 2;
    j--;
    i++;
  }
  assert(sn == n * 2 || sn == 0);
}
