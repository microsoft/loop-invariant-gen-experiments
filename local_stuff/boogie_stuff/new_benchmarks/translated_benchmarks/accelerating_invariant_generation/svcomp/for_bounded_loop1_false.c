int main()
{
  int i = 0;
  int x = 0;
  int y = 0;
  int n = unknown_int();
  assume(n > 0);
  i = 0;
  while (i < n)
  {
    x = x - y;
    assert(x == 0);
    y = unknown_int();
    assume(y != 0);
    x = x + y;
    assert(x != 0);
    i++;
  }
  assert(x == 0);
}
