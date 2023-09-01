int main()
{
  int n, m;
  int x = 0;
  int y;
  n = unknown_int();
  m = unknown_int();
  y = m;
  if (n < 0)
    return;
  if (m < 0)
    return;
  if (m > n - 1)
    return;
  while (x <= n - 1)
  {
    x++;
    if (x >= m + 1)
      y++;
    else if (x > m)
      return;
    x = x;
  }
  if (x < n)
    return;
  assert(!(y >= n + 1));
}