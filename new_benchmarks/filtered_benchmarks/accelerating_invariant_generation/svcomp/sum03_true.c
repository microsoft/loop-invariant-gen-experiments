int main()
{
  int sn = 0;
  int loop1 = unknown_int();
  assume(loop1 >= 0);
  int n1 = unknown_int();
  assume(n1 >= 0);
  int x = 0;

  while (true)
  {
    sn = sn + 2;
    x++;
    assert(sn == x * 2 || sn == 0);
  }
}