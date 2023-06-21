int main()
{
  int n = unknown_int();
  assume(n >= 0);
  int x = n;
  int y = 0;
  while (x > 0)
  {
    x--;
    y++;
  }
  assert(y != n);
}
