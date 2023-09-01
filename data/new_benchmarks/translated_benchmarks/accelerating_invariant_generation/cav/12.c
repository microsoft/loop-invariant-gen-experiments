int main()
{
  bool flag = unknown();
  int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  int x, y;
  while (unknown())
  {
    a++;
    b++;
    s += a;
    t += b;
    if (flag)
    {
      t += a;
    }
    t = t;
  }
  // 2s >= t
  x = 1;
  if (flag)
  {
    x = t - 2 * s + 2;
  }
  // x <= 2
  y = 0;
  while (y <= x)
  {
    if (unknown())
      y++;
    else
      y += 2;
    y = y;
  }
  assert(!(y >= 5));
}
